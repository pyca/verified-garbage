module

public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseCTLit
import VerifiedGarbage.Proof.Ed25519.X86.CommonMemory
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseLit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseCTLit
meta import VerifiedGarbage.Proof.Ed25519.X86.CommonMemory
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseLit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Ed25519.X86.CommonCT
import VerifiedGarbage.Proof.Ed25519.Bytes
meta import VerifiedGarbage.Proof.Ed25519.X86.CommonCT
meta import VerifiedGarbage.Proof.Ed25519.Bytes
public import VerifiedGarbage.Proof.Ed25519.X86.PointCTBlocks
public import VerifiedGarbage.Proof.Ed25519.X86.PointMultiplyFrame
import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ed25519.X86.PointCTBlocks
meta import VerifiedGarbage.Proof.Ed25519.X86.PointMultiplyFrame
meta import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Ed25519.X86.PointBatch
public import VerifiedGarbage.Impl.Ed25519.X86.PointAccumulate
import VerifiedGarbage.Proof.Ed25519.X86.PrepareAdd
meta import VerifiedGarbage.Impl.Ed25519.X86.PointBatch
meta import VerifiedGarbage.Impl.Ed25519.X86.PointAccumulate
meta import VerifiedGarbage.Proof.Ed25519.X86.PrepareAdd
public import VerifiedGarbage.Impl.Ed25519.X86.Comb
import VerifiedGarbage.Proof.Ed25519.X86.CombLit
import VerifiedGarbage.Proof.Ed25519.X86.Point32.AddSum
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Impl.Ed25519.X86.Comb
meta import VerifiedGarbage.Proof.Ed25519.X86.CombLit
meta import VerifiedGarbage.Proof.Ed25519.X86.Point32.AddSum
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Ed25519.Point64Contract
public import VerifiedGarbage.Proof.Ed25519.X86.CombSelect
public import VerifiedGarbage.Proof.Ed25519.X86.Point32.Call
public import VerifiedGarbage.Proof.Ed25519.Group.Double
import VerifiedGarbage.Proof.Ed25519.X86.Point32.Lit
meta import VerifiedGarbage.Proof.Ed25519.Point64Contract
meta import VerifiedGarbage.Proof.Ed25519.X86.CombSelect
meta import VerifiedGarbage.Proof.Ed25519.X86.Point32.Call
meta import VerifiedGarbage.Proof.Ed25519.Group.Double
meta import VerifiedGarbage.Proof.Ed25519.X86.Point32.Lit
meta import Mathlib.Tactic.FieldSimp
meta import Mathlib.Tactic.Ring
public import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseMain
public import VerifiedGarbage.Proof.Framework.X86.SymFrame
public import VerifiedGarbage.Impl.Ed25519.X86.InputBits
public import VerifiedGarbage.Proof.Ed25519.X86.CommonInput
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseMain
meta import VerifiedGarbage.Proof.Framework.X86.SymFrame
meta import VerifiedGarbage.Impl.Ed25519.X86.InputBits
meta import VerifiedGarbage.Proof.Ed25519.X86.CommonInput
meta import VerifiedGarbage.Spec.Ed25519.Contract
meta import VerifiedGarbage.Proof.Framework.Lit

/-! ### `Ed25519.X86.ScalarBaseEntry`, which this module and modules that import it used -/

section

/-! ### `Ed25519.X86.InputBits`, which the modules that import this one used -/

section

/-! Merged from `Proof.Ed25519.X86.BitsExpand`. -/

@[expose] public section

section
/-! Merged from `Proof.Ed25519.X86.BitsExpandStep`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

theorem scalar_store8 {is : List Instr} {s : State} {Q : State → Prop} {b : Reg} {o : Nat} {r : Reg8} {a : Addr}
    (ha : addr (s.gpr b) o = a) (hout : InRegions s.wr a 1)
    (k : ∀ t, Wp.Mupd s t (s.mem.writeW a ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) t Q) :
    WP isa (.block (.store8 ⟨b, o⟩ r :: is)) s Q := by
  refine Wp.cons (s' := { s with mem := s.mem.writeW a ((s.gpr r.reg).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
  change (s.gpr b + BitVec.ofNat 32 o).setWidth 64 = a at ha
  simp only [exec, State.store8, State.ea, ha, hout, ite_true]

theorem doubled_byte_bit (b : Byte) (j : Nat) :
    ((((b.setWidth 32 + b.setWidth 32) >>> (j + 1)) &&& 1).setWidth 8) =
      BitVec.ofNat 8 (b.toNat / 2 ^ j % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_and]
  change (((b.setWidth 32 + b.setWidth 32) >>> (j + 1)).toNat &&& (2 ^ 1 - 1)) % 2 ^ 8 = _
  rw [Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_add, BitVec.toNat_setWidth_of_le (by decide)]
  have hb := b.isLt
  rw [Nat.mod_eq_of_lt (a := b.toNat + b.toNat) (b := 2 ^ 32) (by omega_using [hb]),
    show 2 ^ (j + 1) = 2 * 2 ^ j by rw [Nat.pow_succ'], ← Nat.div_div_eq_div_mul,
    show (b.toNat + b.toNat) / 2 = b.toNat by omega_using []]
  rfl

/-- Bit `j` of the byte at `a` (`[esi]`) to byte `d + j` of the workspace (`[edx + j]`). -/
theorem expandBit_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {a : Addr} {d j : Nat} (hj : j < 8)
    (ha : addr (s.gpr .esi) 0 = a) (hr : InRegions (s.rd ++ s.wr) a 1)
    (hd : addr (s.gpr .edx) j = addr x (d + j)) (hdw : d + j + 1 ≤ 8192) :
    WP isa (.block (expandBit j)) s fun t => (∀ r, r ≠ .eax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.mem = s.mem.writeW (addr x (d + j)) (BitVec.ofNat 8 ((s.mem a).toNat / 2 ^ j % 2)) := by
  refine scalar_ld8 ha hr fun u₁ h₁ => ?_
  refine Wp.wp_add fun u₂ h₂ _ => Wp.wp_shr (by omega_using [hj]) fun u₃ h₃ _ => ?_
  refine Wp.wp_andi fun u₄ h₄ => ?_
  have g : ∀ r, r ≠ .eax → u₄.gpr r = s.gpr r := fun r hr => by
    rw [h₄.other _ hr, h₃.other _ hr, h₂.other _ hr, h₁.other _ hr]
  have w₄ : u₄.wr = s.wr := by rw [h₄.wr, h₃.wr, h₂.wr, h₁.wr]
  refine scalar_store8 (by rw [g .edx (by decide), hd]) (by rw [w₄]; exact hc.inW (by omega_using [hdw]) (by decide))
    fun t ht => WP.block_nil ⟨fun r hr => by rw [ht.gpr, g r hr], by rw [ht.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd],
      by rw [ht.wr, w₄], ?_⟩
  rw [ht.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  change s.mem.writeW _ ((u₄.gpr .eax).setWidth 8) = _
  rw [h₄.gpr, h₃.gpr, h₂.gpr, h₁.gpr, doubled_byte_bit]

theorem bits_byte_write_self (m : Mem) (a : Addr) (v : Byte) : (m.writeW a v) a = v := by
  simp only [Mem.writeW, Mem.write, BitVec.sub_self, BitVec.toNat_zero, Nat.mul_zero]
  apply BitVec.eq_of_toNat_eq
  simp

theorem bits_byte_write_ne (m : Mem) {x : BitVec 32} (v : Byte) {d e : Nat}
    (hd : x.toNat + d + 1 ≤ 2 ^ 32) (he : x.toNat + e + 1 ≤ 2 ^ 32) (h : d ≠ e) :
    (m.writeW (addr x e) v) (addr x d) = m (addr x d) := by
  have hdisj := sub_disj (x := x) (n := 1) (k := 1) hd he (by omega_using [h])
  exact Mem.write_apply fun h' => hdisj _ (Region.contains_self _ _) (by
    simp only [Region.Contains]; omega_using [h'])
end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

/-- The first `n` bits of the byte at `a` (`[esi]`) to bytes `d`, … of the workspace. -/
theorem expandBits_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {a : Addr} {d : Nat}
    (ha : addr (s.gpr .esi) 0 = a) (hr : InRegions (s.rd ++ s.wr) a 1)
    (hd : s.gpr .edx = x + BitVec.ofNat 32 d) (hdw : d + 8 ≤ 8192)
    (hsep : (⟨a, 1⟩ : Region).Disjoint (sub x d 8)) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap expandBit)) s fun t =>
      (∀ r, r ≠ .eax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ Frame [sub x d 8] s.mem t.mem ∧
      ∀ j < n, t.mem (addr x (d + j)) = BitVec.ofNat 8 ((s.mem a).toNat / 2 ^ j % 2)
  | 0, _ => WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    have hfit := hc.fit
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (expandBits_ok hc ha hr hd hdw hsep n (by omega_using [hn]))
      fun u ⟨gu, ru, wu, fu, bu⟩ => ?_)
    have src : u.mem a = s.mem a := fu _ fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hsep _ (Region.contains_self _ _)
    refine WP.mono (expandBit_ok (a := a) (j := n) (d := d) ((Keep.scalar ⟨gu _ (by decide), gu _ (by decide),
        gu _ (by decide), ru, wu⟩).ctx hc) (by omega_using [hn]) (by rw [gu _ (by decide)]; exact ha)
      (by rw [ru, wu]; exact hr)
      (by rw [gu _ (by decide), hd]; simp only [addr, BitVec.add_assoc, BitVec.ofNat_add_ofNat])
      (by omega_using [hn, hdw])) fun t ⟨gt, rt, wt, mt⟩ => ?_
    rw [src] at mt
    refine ⟨fun r hr => by rw [gt r hr, gu r hr], by rw [rt, ru], by rw [wt, wu], ?_, fun j hj => ?_⟩
    · rw [mt]
      exact fu.writeW (List.mem_singleton_self _) _
        (sub_contains (by omega_using [hfit, hdw]) (by omega_using []) (by omega_using [hn]) (by decide))
    · rw [mt]
      by_cases he : j = n
      · subst he; exact bits_byte_write_self _ _ _
      · rw [bits_byte_write_ne _ _ (by omega_using [hfit, hdw, hn, hj])
          (by omega_using [hfit, hdw, hn]) (by omega_using [he])]
        exact bu j (by omega_using [hj, he])

theorem expanded_scalar_bit {p : BitVec 32} (m : Mem) {bytes k : Nat}
    (hp : p.toNat + bytes ≤ 2 ^ 32) (hk : k < 8 * bytes) :
    Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (p.setWidth 64) bytes) / 2 ^ k % 2 =
      (m (addr p (k / 8))).toNat / 2 ^ (k % 8) % 2 := by
  rw [decodeLE_eq]
  have he := Proof.X25519.leNum_bit (Spec.Ed25519.bytesAt m (p.setWidth 64) bytes) k
  simp only [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod] at he
  rw [he]
  simp only [Spec.Ed25519.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by omega_using [hk] : k / 8 < bytes), Option.map_some, Option.getD_some]
  rw [addr_eq (by omega_using [hp, hk])]

theorem expandScalarBits_ok {x p : BitVec 32} {s : State} (hc : Ctx x s)
    (hp : s.gpr .esi = p) {bytes : Nat} (hb : bytes ≤ 64) (hb1 : 1 ≤ bytes)
    (hfit : p.toNat + bytes ≤ 2 ^ 32)
    (hr : ∀ i < bytes, InRegions (s.rd ++ s.wr) (addr p i) 1)
    (hs : ∀ i < bytes, (sub p i 1).Disjoint (sub x 7168 (8 * bytes))) :
    WP isa (expandScalarBits bytes) s fun t => ScalarKeep s t ∧ Frame [sub x 7168 (8 * bytes)] s.mem t.mem ∧
      ∀ k < 8 * bytes, t.mem (addr x (7168 + k)) = BitVec.ofNat 8
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (p.setWidth 64) bytes) / 2 ^ k % 2) := by
  have hx := hc.fit
  -- After `i` bytes.
  let LI : Nat → State → Prop := fun i t => ScalarKeep s t ∧ t.gpr .esi = p + BitVec.ofNat 32 i ∧
    t.gpr .edx = x + BitVec.ofNat 32 (7168 + 8 * i) ∧ t.gpr .ecx = BitVec.ofNat 32 (bytes - i) ∧
    Frame [sub x 7168 (8 * bytes)] s.mem t.mem ∧
    ∀ k < 8 * i, t.mem (addr x (7168 + k)) = BitVec.ofNat 8 ((s.mem (addr p (k / 8))).toNat / 2 ^ (k % 8) % 2)
  unfold expandScalarBits
  refine WP.seq (Wp.wp_mov fun u₁ v₁ => Wp.wp_addi fun u₂ v₂ => Wp.wp_movi fun u₃ v₃ => WP.block_nil ?_)
  refine (WP.loop (M := isa) (Q := LI bytes) (fun m t => ∃ i, m = bytes - i ∧ i < bytes ∧ LI i t) ?_ bytes u₃
    ⟨0, by omega_arith, by omega_arith, ⟨by rw [v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide)],
      by rw [v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide)],
      by rw [v₃.rd, v₂.rd, v₁.rd], by rw [v₃.wr, v₂.wr, v₁.wr]⟩,
      by rw [v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide), hp]; simp,
      by rw [v₃.other _ (by decide), v₂.gpr, v₁.gpr, hc.edi]; rfl, by rw [v₃.gpr]; rfl,
      by rw [v₃.mem, v₂.mem, v₁.mem]; exact Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩).mono ?_
  · rintro m t ⟨i, rfl, hi, kt, si, di, ci, ft, bt⟩
    have ct := kt.ctx hc
    have src : t.mem (addr p i) = s.mem (addr p i) := ft _ fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (hs i hi) _ (by rw [sub]; exact Region.contains_self _ _)
    have sep : (⟨addr p i, 1⟩ : Region).Disjoint (sub x (7168 + 8 * i) 8) :=
      (hs i hi).sub_right (sub_sub hx (by omega_using []) (by omega_using [hi]) (by omega_using [hi, hb]))
    unfold expandByte
    refine WP.block_append (WP.mono (expandBits_ok ct (a := addr p i) (d := 7168 + 8 * i)
      (by rw [si]; simp only [addr, BitVec.add_zero])
      (by rw [kt.rd, kt.wr]; exact hr i hi) di (by omega_using [hi, hb]) sep 8 (Nat.le_refl _))
      fun u ⟨gu, ru, wu, fu, bu⟩ => ?_)
    refine Wp.wp_addi fun w₁ y₁ => Wp.wp_addi fun w₂ y₂ => Wp.wp_subi fun w₃ y₃ _ z₃ => WP.block_nil ?_
    have next : LI (i + 1) w₃ := by
      refine ⟨kt.trans ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, fun k hk => ?_⟩
      · rw [y₃.other _ (by decide), y₂.other _ (by decide), y₁.other _ (by decide), gu _ (by decide)]
      · rw [y₃.other _ (by decide), y₂.other _ (by decide), y₁.other _ (by decide), gu _ (by decide)]
      · rw [y₃.rd, y₂.rd, y₁.rd, ru]
      · rw [y₃.wr, y₂.wr, y₁.wr, wu]
      · rw [y₃.other _ (by decide), y₂.other _ (by decide), y₁.gpr, gu _ (by decide), si,
          show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      · rw [y₃.other _ (by decide), y₂.gpr, y₁.other _ (by decide), gu _ (by decide), di,
          show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
          show 7168 + 8 * i + 8 = 7168 + 8 * (i + 1) by omega_arith]
      · rw [y₃.gpr, y₂.other _ (by decide), y₁.other _ (by decide), gu _ (by decide), ci,
          Wp.ofNat_pred (by omega_arith)]
        congr 1
      · rw [y₃.mem, y₂.mem, y₁.mem]
        exact ft.trans (fu.sub fun r hr => ⟨_, List.mem_singleton_self _, by
          rw [List.mem_singleton.mp hr]
          exact sub_sub hx (by omega_using []) (by omega_using [hi]) (by omega_using [hi, hb])⟩)
      · rw [y₃.mem, y₂.mem, y₁.mem]
        by_cases e : k < 8 * i
        · rw [← bt k e]
          refine fu _ fun r hr => ?_
          rw [List.mem_singleton.mp hr]
          exact sub_disj (x := x) (d := 7168 + k) (n := 1) (e := 7168 + 8 * i) (k := 8)
            (by omega_using [hx, hk, hi, hb]) (by omega_using [hx, hi, hb]) (.inl (by omega_using [e])) _
            (Region.contains_self _ _)
        · have := bu (k - 8 * i) (by omega_using [hk, e])
          rw [show 7168 + 8 * i + (k - 8 * i) = 7168 + k by omega_arith] at this
          rw [this, src, show k / 8 = i by omega_arith, show k % 8 = k - 8 * i by omega_arith]
    have z : w₃.zf = some (decide (bytes - (i + 1) = 0)) := by
      rw [z₃, y₂.other _ (by decide), y₁.other _ (by decide), gu _ (by decide), ci, Wp.ofNat_pred (by omega_arith),
        Wp.ofNat_beq_zero (by omega_arith)]
      rfl
    by_cases done : i + 1 = bytes
    · refine .inl ⟨?_, done ▸ next⟩
      simp only [eval, z, show bytes - (i + 1) = 0 by omega_arith, decide_true, Option.map_some, Bool.not_true]
    · refine .inr ⟨?_, bytes - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, next⟩
      simp only [eval, z, show bytes - (i + 1) ≠ 0 by omega_arith, decide_false, Option.map_some, Bool.not_false]
  · rintro t ⟨kt, _, _, _, ft, bt⟩
    refine ⟨kt, ft, fun k hk => ?_⟩
    rw [bt k hk, expanded_scalar_bit s.mem hfit hk]

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

theorem inputByte_contains {s₀ : State} {scidx i n : Nat} (hp : InputPre s₀ scidx i n)
    {k : Nat} (hk : k < 4 * n) : (sub (arg s₀ i) 0 (4 * n)).Contains (addr (arg s₀ i) k) 1 :=
  sub_contains (by have := hp.fit; omega_using [this]) (Nat.zero_le _) (by omega_using [hk]) (by decide)

theorem inputBytes_same {s₀ s : State} {scidx i n : Nat} (hp : InputPre s₀ scidx i n)
    (hs : Saved s₀ (arg s₀ scidx) s) :
    Spec.Ed25519.bytesAt s.mem ((arg s₀ i).setWidth 64) (4 * n) =
      Spec.Ed25519.bytesAt s₀.mem ((arg s₀ i).setWidth 64) (4 * n) := by
  apply List.map_congr_left
  intro k hk
  have hk' := List.mem_range.mp hk
  rw [← addr_eq (by have := hp.fit; omega_using [this, hk'])]
  apply hs.frame
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.sep _ (inputByte_contains hp hk')
  · exact hp.stk _ (inputByte_contains hp hk')

/-- `inputBits`, which writes only the bits' bytes of the workspace. -/
theorem inputBits_frame {s₀ s : State} {scidx argc i n : Nat}
    (hp : ScratchPre s₀ scidx argc) (hi : InputPre s₀ scidx i n)
    (hs : Saved s₀ (arg s₀ scidx) s) (hia : i < argc) (hn : n ≤ 16) (hn1 : 1 ≤ n) :
    WP isa (inputBits i (4 * n)) s fun t => Saved s₀ (arg s₀ scidx) t ∧
      Frame [sub (arg s₀ scidx) 7168 (8 * (4 * n))] s.mem t.mem ∧ (∀ k < 32 * n, t.mem (addr (arg s₀ scidx) (7168 + k)) = BitVec.ofNat 8
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ i).setWidth 64) (4 * n)) / 2 ^ k % 2)) := by
  unfold inputBits
  refine WP.seq (WP.mono (loadArg_ok hp hs hia) fun u ⟨hu, eu, mu⟩ => ?_)
  have cu := hu.ctx hp.fit hp.wr hp.stk
  have hr : ∀ k < 4 * n, InRegions (u.rd ++ u.wr) (addr (arg s₀ i) k) 1 := by
    intro k hk; refine ⟨_, ?_, inputByte_contains hi hk⟩
    rw [hu.rd, hu.wr]; exact hi.rd
  have hsep : ∀ k < 4 * n, (sub (arg s₀ i) k 1).Disjoint (sub (arg s₀ scidx) 7168 (8 * (4 * n))) := by
    intro k hk
    refine (hi.sep.sub_left ?_).sub_right ?_
    · rw [sub, sub, addr_eq (by have := hi.fit; omega_using [this, hk]), addr_zero]
      exact Offset.sub_base _ (by omega_using [hk])
    · rw [scR_eq]; exact sub_sub hp.fit (by decide) (by omega_using [hn]) (by decide)
  refine WP.mono (expandScalarBits_ok cu eu (by omega_using [hn]) (by omega_using [hn1]) hi.fit hr hsep)
    fun t ⟨kt, ft, bt⟩ => ?_
  refine ⟨hu.of_offset hp.fit kt ft (by decide) (by omega_using [hn]) (by decide),
    by rw [← mu]; exact ft, fun k hk => ?_⟩
  rw [bt k (by omega_using [hk]), inputBytes_same hi hu]

end VG.Proof.Ed25519.X86

end

end

/-!
# The comb's tables' address at the entry of `vg_ed25519_scalar_base` and `vg_x25519_base`

`combAddr 2` forms the static's address in a balanced four-byte CALL frame below `esp`
(`symFrame_ok`) and stores it at byte `combTbl` of the workspace: the rest of the function
starts (`BodyPre`) from the same regions and arguments, with the address there and the tables
readable (`TblAt`), and what it preserves of its own start the function preserves of its entry
(`Prologue`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

/-- What the function's body needs. -/
def BodyPre (s : State) : Prop :=
  BaseRegions s ∧ wd s.mem (arg s 2) combTbl = s.syms combSym ∧
    TblAt (arg s 2) (s.syms combSym) s ∧ (TBL ((s.syms combSym).setWidth 64)).Disjoint (callStk s)

/-- The state `t` after the prologue, from the entry `s`. -/
structure Prologue (s t : State) : Prop where
  pre : BodyPre t
  gpr : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  ret : t.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32
  args : ∀ j < 3, arg t j = arg s j
  input : Spec.Ed25519.bytesAt t.mem ((arg s 1).setWidth 64) 32 =
    Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32
  syms : t.syms = s.syms

/-- The static's address's frame, within the stack a call uses. -/
theorem below4_sub {sp : BitVec 32} (h : 8 ≤ sp.toNat) :
    Region.Sub (below sp 4) ⟨(sp - BitVec.ofNat 32 8).setWidth 64, 8⟩ := by
  simp only [below, Taint.sub_setWidth (show 4 ≤ sp.toNat by omega_using [h]), Taint.sub_setWidth h]
  exact Offset.sub_below _ (by decide) (by decide)

theorem combAddr_ok {s : State} (h : scalarBaseLocal.pre s) : WP isa (combAddr 2) s (Prologue s) := by
  obtain ⟨hr, _, held⟩ := h
  obtain ⟨hp, hi, _⟩ := scalarBase_pre hr
  have h20 := hp.stk.1
  have hsp : 4 ≤ (s.gpr .esp).toNat := by omega_using [h20]
  have s4 := below4_sub h20
  have ki : (below (s.gpr .esp) 4).Disjoint ⟨(arg s 1).setWidth 64, 32⟩ := hr.2.2.2.2.2.2.2.2.2.2.2.2.2.1.sub_left s4
  have hspfit := hp.sp_fit
  have hl := combWords_length
  refine WP.seq (WP.mono (symFrame_ok combSym s hsp) fun s₁ P => ?_)
  have e1 : s₁.gpr .esp = s.gpr .esp := P.gpr .esp (by decide)
  have a1 : ∀ j < 3, arg s₁ j = arg s j := fun j hj => P.arg hsp (by omega_using [hspfit, hj])
  refine Wp.wp_ldm e1 (by rw [P.rd, P.wr]; exact hp.argIn hp.index) fun s₂ h₂ => ?_
  have e2 : s₂.gpr .edx = arg s 2 := by
    rw [h₂.gpr, ← a1 2 (by decide)]
    simp only [arg, argAddr, e1]
    rfl
  have hw : InRegions s₂.wr (addr (arg s 2) combTbl) 4 := by
    rw [h₂.wr, P.wr]
    exact ⟨_, hp.wr, scR_contains hp.fit (by decide) (by decide)⟩
  refine Wp.wp_stm e2 hw fun s₃ h₃ => WP.block_nil ?_
  have hsub : ∀ r : Reg, r ∈ [Reg.eax, .ecx] → r ∈ [Reg.eax, .ecx, .edx] := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl <;> simp
  have g3 : ∀ r, r ∉ [Reg.eax, .ecx, .edx] → s₃.gpr r = s.gpr r := fun r hr => by
    rw [h₃.gpr, h₂.other r (fun e => hr (by subst e; decide)), P.gpr r (fun e => hr (hsub r e))]
  have e3 : s₃.gpr .esp = s.gpr .esp := g3 .esp (by decide)
  have r3 : s₃.rd = s.rd := by rw [h₃.rd, h₂.rd, P.rd]
  have w3 : s₃.wr = s.wr := by rw [h₃.wr, h₂.wr, P.wr]
  have y3 : s₃.syms = s.syms := by rw [h₃.syms, h₂.syms, P.syms]
  -- The store, to the workspace.
  have G : Frame [scR 8192 (arg s 2)] s₁.mem s₃.mem := by
    rw [h₃.mem, h₂.mem]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (scR_contains hp.fit (by decide) (by decide))
  -- Everything: the frame below `esp` and the store.
  have F : Frame [below (s.gpr .esp) 4, scR 8192 (arg s 2)] s.mem s₃.mem :=
    (P.frame.mono fun r hr => by
      rw [List.mem_singleton.mp hr]; exact List.mem_cons_self).trans
      (G.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  have a3 : ∀ j < 3, arg s₃ j = arg s j := by
    intro j hj
    rw [← a1 j hj]
    simp only [arg, argAddr, e3, e1]
    refine G.readW (r := ⟨argAddr s 0, 12⟩) ?_ ?_ (by decide)
    · exact hp.arg_contains (i := j) hj
    · intro r hr; rw [List.mem_singleton.mp hr]; exact hp.args_sc
  have T3 : TblWords ((s.syms combSym).setWidth 64) s₃.mem := fun i hi => by
    rw [← held.1 i hi]
    refine F.readW (r := TBL ((s.syms combSym).setWidth 64)) (Offset.contains_base _ (by omega_using [hi])
      (by omega_using [hl, hi])) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (held.2.2 _ (by simp)).sub_right s4
    · exact held.2.2 _ (by simp)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, fun r hr => g3 r ?_, ?_, a3, ?_, y3⟩
  · simpa only [BaseRegions, argAddr, callStk, e3, r3, w3, y3, a3 0 (by decide), a3 1 (by decide),
      a3 2 (by decide)] using hr
  · rw [a3 2 (by decide), y3, h₃.mem, wd_write_self, h₂.other .eax (by decide), P.addr]
  · rw [a3 2 (by decide), y3]
    exact ⟨held.2.1, by rw [r3, hr.1]; simp, T3, held.2.2 _ (by simp)⟩
  · rw [y3, callStk, e3]; exact held.2.2 _ (by simp)
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [← P.ret hsp (by omega_using [hspfit])]
    refine G.readW (r := ⟨(s.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr; rw [List.mem_singleton.mp hr]; exact hp.ret_sc
  · unfold Spec.Ed25519.bytesAt
    have hs := hi.sep
    rw [sub, addr_zero] at hs
    refine List.map_congr_left fun k hk =>
      F.bytes (R := ⟨(arg s 1).setWidth 64, 32⟩) ?_ (by change 32 ≤ 2 ^ 64; decide)
        (List.mem_range.mp hk)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ki.symm
    · exact hs

/-- The regions and arguments survive the static's address's frame. -/
theorem BaseRegions.symAddr {name : String} {s t : State} (h : BaseRegions s)
    (P : SymAddrPost name s t) (hsp : 4 ≤ (s.gpr .esp).toNat) : BaseRegions t := by
  have hf : (s.gpr .esp).toNat + 16 ≤ 2 ^ 32 := h.2.2.2.2.2.2.2.2.2.2.2.1
  have e : t.gpr .esp = s.gpr .esp := P.gpr .esp (by decide)
  have a : ∀ j < 3, arg t j = arg s j := fun j hj => P.arg hsp (by omega_using [hf, hj])
  simpa only [BaseRegions, argAddr, callStk, e, P.rd, P.wr, P.syms, a 0 (by decide), a 1 (by decide),
    a 2 (by decide)] using h

/-- The public part of the states after the prologue. -/
theorem Prologue.pub {s t u v : State} (Pu : Prologue s u) (Pv : Prologue t v)
    (h : scalarBaseLocal.pub s t) : scalarBaseLocal.pub u v := by
  obtain ⟨sp, a0, a1, a2, sy⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Pu.gpr .esp (by decide), Pv.gpr .esp (by decide), sp]
  · rw [Pu.args 0 (by decide), Pv.args 0 (by decide), a0]
  · rw [Pu.args 1 (by decide), Pv.args 1 (by decide), a1]
  · rw [Pu.args 2 (by decide), Pv.args 2 (by decide), a2]
  · rw [Pu.syms, Pv.syms, sy]

/-- The function preserves of its entry what its body preserves of its start. -/
theorem Prologue.abi {s s' t : State} (h : Prologue s s') (ha : abiPreserved s' t) :
    abiPreserved s t := by
  refine ⟨fun r hr => (ha.1 r hr).trans (h.gpr r hr), ?_⟩
  have he := h.gpr .esp (by decide)
  have := ha.2
  rw [he] at this
  exact this.trans h.ret

end VG.Proof.Ed25519.X86

end

end

/-! ### `Ed25519.X86.CombLoop`, which this module and modules that import it used -/

section

/-! ### `Ed25519.PointDouble`, which only this module used -/

section

/-!
# RFC 8032's doubling represents the double

`Point64.pointDouble`, RFC 8032's doubling formula (§5.1.4), is `dblPoint`
(`dbl-2008-hwcd`) with every coordinate negated (`pointDouble_neg`), the same
point: it represents `a + a` for any `X : Y : Z` representing `a`
(`pointDouble_rep`), whatever `T` is.
-/

@[expose] public section

namespace VG.Proof.Ed25519

open Spec.X25519 (Fe)
open Spec.Ed25519 (Point)
open Edwards

theorem pointDouble_neg (p : Point) :
    Proof.Ed25519.Point64.pointDouble p =
      ⟨-(dblPoint p).X, -(dblPoint p).Y, -(dblPoint p).Z, -(dblPoint p).T⟩ := by
  simp only [Proof.Ed25519.Point64.pointDouble, dblPoint]
  congr 1 <;> grind

private theorem toZ_neg' (a : Fe) : toZ (-a) = -toZ a := rfl

theorem pointDouble_rep {p : Point} {a : EPoint dZ} (h : RepP p a) :
    Rep (Proof.Ed25519.Point64.pointDouble p) (a + a) := by
  obtain hr := dblPoint_rep h
  rw [pointDouble_neg]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show toZ (-_) ≠ 0
    rw [toZ_neg']; exact neg_ne_zero.mpr hr.z
  · show toZ (-_) = _ * toZ (-_)
    rw [toZ_neg', toZ_neg', hr.x, mul_neg]
  · show toZ (-_) = _ * toZ (-_)
    rw [toZ_neg', toZ_neg', hr.y, mul_neg]
  · show toZ (-_) = _ * toZ (-_)
    rw [toZ_neg', toZ_neg', hr.t, mul_neg]

end VG.Proof.Ed25519

end

end


/-!
# The comb's loop

The mixed additions (`addEvenOps` inline, and `vg_ed25519_r32_add_affine`'s
calls) add an affine cached point exactly as the specification's `pointAdd`;
`combNeg` negates the selected entry under its sign's mask; the doublings are
calls of `vg_ed25519_r32_double`, RFC 8032's (`pointDouble_rep`); after step
`j`, the accumulator `A` (slots 0–3)
represents `[G + Σ_{i < j} d_{2i+1} 256^i]B` and `B` (slots 17–20) represents
`[G + Σ_{i < j} d_{2i} 256^i]B` (`Proof/Ed25519/CombDigits.lean`); at the end,
`16 A + B` is the scalar's multiple.
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519 VG.Impl.Ed25519.X86 VG.Proof.Ed25519 Edwards
open VG.Impl.X25519.X86 (sc)

/-! ## Frames -/

theorem MulKeep.of_field {x : BitVec 32} {s t : State} (hc : Ctx x s) (h : FieldKeep x s t) :
    MulKeep x s t := MulKeep.of_ikeep hc (IKeep.of_field h)

theorem MulKeep.of_call {x : BitVec 32} {s t : State} (hc : Ctx x s) (h : CallKeep x s t) :
    MulKeep x s t := MulKeep.of_ikeep hc (IKeep.of_call h)

theorem MulKeep.of_digit {x : BitVec 32} {s t : State} (hc : Ctx x s) (h : DigitKeep x s t) :
    MulKeep x s t := by
  refine ⟨h.keep.edi, h.keep.esp, h.keep.rd, h.keep.wr, h.frame.sub fun r hr => ?_⟩
  rw [List.mem_singleton.mp hr]
  exact ⟨sub x 24 7144, List.mem_cons_self .., sub_sub hc.fit (by omega_arith) (by omega_arith) (by omega_arith)⟩

theorem MulKeep.of_sel {x : BitVec 32} {s t : State} (hc : Ctx x s) (k : Keep s t)
    (h : SelFrame x s.mem t.mem) : MulKeep x s t :=
  ⟨k.edi, k.esp, k.rd, k.wr, h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨sub x 24 7144, List.mem_cons_self .., ?_⟩
    rcases hr with rfl | rfl
    · exact sub_sub hc.fit (by decide) (by decide) (by decide)
    · exact sub_sub hc.fit (by decide) (by decide) (by decide)⟩

/-- The tables survive the comb's writes, to the workspace and the stack a call uses. -/
theorem TblAt.mulkeep {x P : BitVec 32} {s t : State} (h : TblAt x P s) (hc : Ctx x s)
    (hstk : (TBL (P.setWidth 64)).Disjoint (callStk s)) (k : MulKeep x s t) : TblAt x P t := by
  have hl := combWords_length
  refine ⟨h.fit, k.rd ▸ h.rd, fun i hi => ?_, h.far⟩
  rw [← h.words i hi]
  refine k.frame.readW (r := TBL (P.setWidth 64)) (Offset.contains_base _ (by omega_arith) (by omega_arith))
    (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.far.sub_right (by rw [scR_eq]; exact sub_sub hc.fit (by decide) (by decide) (by decide))
  · exact hstk

/-! ## The mixed additions -/

theorem addEven_formula (e : Env) :
    point (evalOps addEvenOps e) 17 18 19 20 =
      Point32.mixedResult (e 17) (e 18) (e 19) (e 20) (e 13) (e 14) (e 15) := rfl

theorem mixed_eval {e : Env} {a b c : Slot} {q : Spec.Ed25519.Point}
    (hq : cachedAt e a b c = cache q) (p : Spec.Ed25519.Point) (hz : q.Z = 1) :
    Point32.mixedResult p.X p.Y p.Z p.T (e a) (e b) (e c) = Spec.Ed25519.pointAdd p q := by
  obtain h4 : e a = q.Y - q.X := congrArg Spec.Ed25519.Point.X hq
  obtain h5 : e b = q.Y + q.X := congrArg Spec.Ed25519.Point.Y hq
  obtain h6 : e c = q.T * 2 * Spec.Ed25519.d := congrArg Spec.Ed25519.Point.Z hq
  rw [h4, h5, h6, Point32.mixedResult_eq p q hz]

theorem addEven_ok {s : State} {x : BitVec 32} (hc : Ctx x s)
    (q : Spec.Ed25519.Point) (hq : cachedAt (env s.mem x) 13 14 15 = cache q) (hz : q.Z = 1) :
    WP isa (.block (fieldCode addEvenOps)) s fun t =>
      FieldKeep x s t ∧ point (env t.mem x) 17 18 19 20 =
        Spec.Ed25519.pointAdd (point (env s.mem x) 17 18 19 20) q ∧
      ∀ i : Slot, (i.val < 8 ∨ 13 ≤ i.val ∧ i.val < 17 ∨ 21 ≤ i.val) →
        env t.mem x i = env s.mem x i := by
  refine WP.mono (fieldCode_ok addEvenOps hc) fun t ⟨hk, hv⟩ => ?_
  rw [hv]
  refine ⟨hk, (addEven_formula _).trans (mixed_eval hq (point (env s.mem x) 17 18 19 20) hz),
    fun i hi => ?_⟩
  apply evalOps_unchanged
  intro op hop h
  have : ∀ op ∈ addEvenOps, (8 ≤ (fieldDest op).val ∧ (fieldDest op).val < 13) ∨
      (17 ≤ (fieldDest op).val ∧ (fieldDest op).val < 21) := by decide
  have := this op hop
  rw [← h] at this
  omega_arith

/-! ## The negations -/

/-- The negation, on the environment. -/
theorem neg_env (e : Env) (a b c : Slot) (sw : Bool) (hab : a ≠ b) (hc8 : c ≠ 8) (ha : a ≠ 8)
    (hb : b ≠ 8) (hac : a ≠ c) (hbc : b ≠ c) (hz : e 21 = 0) :
    cachedAt (swapsEnv [(a, b), (c, 8)] sw (evalOps [.sub 8 21 c] e)) a b c =
      if sw then negCached (cachedAt e a b c) else cachedAt e a b c := by
  cases sw <;> simp [cachedAt, negCached, swapsEnv, swapEnv, evalOps, evalOp,
    hab, hc8, ha, hb, ha.symm, hb.symm, hac, hac.symm, hbc, hbc.symm, hz]

theorem neg_other (e : Env) (a b c : Slot) (sw : Bool) (i : Slot) (ha : i ≠ a) (hb : i ≠ b)
    (hc : i ≠ c) (h8 : i ≠ 8) :
    swapsEnv [(a, b), (c, 8)] sw (evalOps [.sub 8 21 c] e) i = e i := by
  cases sw <;> simp [swapsEnv, swapEnv, evalOps, evalOp, Function.update_apply, ha, hb, hc, h8]

theorem combNeg_ok {s : State} {x : BitVec 32} (hc : Ctx x s) (a b c : Slot) {sign : Nat}
    (hs1 : 928 ≤ sign) (hs2 : sign + 4 ≤ 8192) (sw : Bool) (hm : wd s.mem x sign = mask sw.toNat)
    (hdis : ∀ p ∈ [(a, b), (c, (8 : Slot))], p.1 ≠ p.2) :
    WP isa (.block (combNeg a b c sign)) s fun t => FieldKeep x s t ∧
      env t.mem x = swapsEnv [(a, b), (c, 8)] sw (evalOps [.sub 8 21 c] (env s.mem x)) := by
  rw [combNeg, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fieldCode_ok [.sub 8 21 c] hc) fun u ⟨ku, vu⟩ => ?_
  obtain cu := ku.ctx hc
  rw [List.singleton_append]
  refine Wp.wp_ldm cu.edi (cu.inRW hs2 (by decide)) fun v hv => ?_
  obtain kv : FieldKeep x u v := FieldKeep.of_mem (updKeep hv) hv.mem
  obtain hmv : v.gpr .ecx = mask sw.toNat := by
    rw [hv.gpr]
    change wd u.mem x sign = _
    rw [wd_frame1 ku.frame hc.fit (by decide) hs2 (Or.inr (by omega_arith))]
    exact hm
  refine WP.mono (swapFields_ok (kv.ctx cu) _ hdis sw hmv) fun t ⟨kt, _, vt⟩ =>
    ⟨(ku.trans kv).trans kt, ?_⟩
  rw [vt, hv.mem, vu]

/-! ## Four doublings -/

structure Double4Inv (x : BitVec 32) (s₀ : State) (a : EPoint dZ) (n : Nat) (s : State) : Prop where
  lo : 1 ≤ n
  hi : n ≤ 4
  keep : IKeep x s₀ s
  counter : s.gpr .esi = BitVec.ofNat 32 n
  value : Rep (point (env s.mem x) 0 1 2 3) ((2 ^ (4 - n) : Nat) • a)
  high : ∀ i : Slot, 16 ≤ i.val → env s.mem x i = env s₀.mem x i

/-- A doubling, a call of `vg_ed25519_r32_double`, and the counter's decrement. -/
theorem doubleStep_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {n : Nat}
    (hn : 1 ≤ n) (hn' : n < 2 ^ 32) (hb : s.gpr .esi = BitVec.ofNat 32 n) :
    WP isa (.seq Point32.doubleCall (.block [.alu .sub .esi (.imm 1)])) s fun t =>
      IKeep x s t ∧ t.gpr .esi = BitVec.ofNat 32 (n - 1) ∧
      isa.eval .ne t = some (!decide (n - 1 = 0)) ∧
      point (env t.mem x) 0 1 2 3 = Proof.Ed25519.Point64.pointDouble (point (env s.mem x) 0 1 2 3) ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem x i = env s.mem x i := by
  refine WP.seq (WP.mono (doubleCall_ok hc) fun t ⟨ht, pt, high⟩ => ?_)
  refine Wp.wp_subi fun u hu _ hz => WP.block_nil ?_
  refine ⟨(IKeep.of_call ht).trans (IKeep.of_counter hu), ?_, ?_, ?_, ?_⟩
  · rw [hu.gpr, ht.keep.esi, hb]; exact Wp.ofNat_pred hn
  · show u.zf.map (!·) = _
    rw [hz, ht.keep.esi, hb, Wp.ofNat_pred hn, Wp.ofNat_beq_zero (by omega_using [hn'])]
    rfl
  · rw [hu.mem]; exact pt
  · rw [hu.mem]; exact high

theorem double4_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {a : EPoint dZ}
    (ha : Rep (point (env s.mem x) 0 1 2 3) a) :
    WP isa double4 s fun t => IKeep x s t ∧
      Rep (point (env t.mem x) 0 1 2 3) ((16 : Nat) • a) ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem x i = env s.mem x i := by
  refine WP.seq (Wp.wp_movi fun t ht => WP.block_nil ?_)
  refine WP.loop (M := isa) (Inv := Double4Inv x s a) ?_ 4 t
    ⟨by decide, by decide, IKeep.of_counter ht, ht.gpr, ?_, ?_⟩
  · intro n u h
    refine WP.mono (doubleStep_ok (h.keep.ctx hc) h.lo (by omega_using [h.hi]) h.counter)
      fun v ⟨kv, bv, zv, pv, high⟩ => ?_
    obtain kk := h.keep.trans kv
    obtain pp : Rep (point (env v.mem x) 0 1 2 3) ((2 ^ (4 - (n - 1)) : Nat) • a) := by
      rw [pv, show 4 - (n - 1) = (4 - n) + 1 by omega_using [h.lo, h.hi],
        show (2 ^ ((4 - n) + 1) : Nat) = 2 ^ (4 - n) + 2 ^ (4 - n) by rw [pow_succ]; omega_arith, add_nsmul]
      exact pointDouble_rep h.value.proj
    obtain hh : ∀ i : Slot, 16 ≤ i.val → env v.mem x i = env s.mem x i :=
      fun i hi => (high i hi).trans (h.high i hi)
    by_cases hn : n = 1
    · subst n
      exact .inl ⟨by rw [zv]; rfl, kk, pp, hh⟩
    · exact .inr ⟨by rw [zv]; simp only [show n - 1 ≠ 0 by omega_using [hn, h.lo], decide_false]; rfl,
        n - 1, by omega_using [h.lo], by omega_using [hn, h.lo], by omega_using [h.hi], kk, bv, pp, hh⟩
  · rw [ht.mem, show (2 ^ (4 - 4) : Nat) = 1 from rfl, one_nsmul]; exact ha
  · rw [ht.mem]; exact fun _ _ => rfl

/-! ## The loop -/

theorem digit_env {x : BitVec 32} {m m' : Mem} (hf : Frame [sub x 1024 136] m m')
    (hx : x.toNat + 8192 ≤ 2 ^ 32) : env m' x = env m x := by
  funext i
  have hi := i.isLt
  exact congrArg VG.Proof.X25519.toFe (fe_frame fun k hk =>
    wd_frame1 hf hx (by decide) (by simp only [offset]; omega_arith) (Or.inl (by simp only [offset]; omega_arith)))

theorem sel_env {x : BitVec 32} {m m' : Mem} (hf : SelFrame x m m') (hx : x.toNat + 8192 ≤ 2 ^ 32)
    (i : Slot) (hi : i.val < 4 ∨ (7 ≤ i.val ∧ i.val < 13) ∨ 16 ≤ i.val) : env m' x i = env m x i := by
  have hl := i.isLt
  exact congrArg VG.Proof.X25519.toFe (fe_frame fun k hk => wd_frame hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sub_disj (by simp only [offset]; omega_arith) (by simp only [offset]; omega_arith)
        (by simp only [offset]; omega_arith)
    · exact sub_disj (by simp only [offset]; omega_arith) (by simp only [offset]; omega_arith)
        (by simp only [offset]; omega_arith))

theorem combNext_ok {s : State} {j : Nat} (hj : j < 32) (h : s.gpr .esi = BitVec.ofNat 32 j) :
    WP isa (.block [.alu .add .esi (.imm 1), .alu .cmp .esi (.imm 32)]) s fun t =>
      t.gpr .esi = BitVec.ofNat 32 (j + 1) ∧ isa.eval .ne t = some (!decide (j + 1 = 32)) ∧
      t.gpr .edi = s.gpr .edi ∧ t.gpr .esp = s.gpr .esp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mem = s.mem := by
  refine Wp.wp_addi fun u hu => Wp.wp_cmpi fun t ht _ zt => WP.block_nil ?_
  obtain e : u.gpr .esi = BitVec.ofNat 32 (j + 1) := by rw [hu.gpr, h, BitVec.ofNat_add]; rfl
  refine ⟨by rw [ht.gpr, e], ?_, by rw [ht.gpr, hu.other .edi (by decide)],
    by rw [ht.gpr, hu.other .esp (by decide)], by rw [ht.rd, hu.rd], by rw [ht.wr, hu.wr],
    by rw [ht.mem, hu.mem]⟩
  show t.zf.map (!·) = _
  rw [zt, e, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl, Wp.sub_beq (by omega_arith) (by omega_arith)]
  rfl

/-- The loop's invariant, after `j` steps, with the tables' address `P`. -/
structure CombInv (x : BitVec 32) (s₀ : State) (S : Nat) (P : BitVec 32) (j : Nat) (s : State) :
    Prop where
  bound : j ≤ 32
  keep : MulKeep x s₀ s
  counter : s.gpr .esi = BitVec.ofNat 32 j
  ptr : wd s.mem x combTbl = P
  zero : env s.mem x 21 = 0
  d : env s.mem x 16 = Spec.Ed25519.d
  odd : Rep (point (env s.mem x) 0 1 2 3) ((combGVal + oddSumZ S j) • baseAff)
  even : Rep (point (env s.mem x) 17 18 19 20) ((combGVal + evenSumZ S j) • baseAff)

private theorem dis_odd : ∀ ab ∈ [((4 : Slot), (5 : Slot)), (6, 8)], ab.1 ≠ ab.2 := by
  intro ab hab; simp only [List.mem_cons, List.not_mem_nil, or_false] at hab
  rcases hab with rfl | rfl <;> decide

private theorem dis_even : ∀ ab ∈ [((13 : Slot), (14 : Slot)), (15, 8)], ab.1 ≠ ab.2 := by
  intro ab hab; simp only [List.mem_cons, List.not_mem_nil, or_false] at hab
  rcases hab with rfl | rfl <;> decide

theorem combStep_ok {x P : BitVec 32} {s₀ s : State} (hc₀ : Ctx x s₀) {S j : Nat}
    (hb : ∀ q < 256, s₀.mem (addr x (7168 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2))
    (ht₀ : TblAt x P s₀) (hts : (TBL (P.setWidth 64)).Disjoint (callStk s₀))
    (h : CombInv x s₀ S P j s) (hj : j < 32) :
    WP isa combStep s fun t => isa.eval .ne t = some (!decide (j + 1 = 32)) ∧
      CombInv x s₀ S P (j + 1) t := by
  obtain hc := h.keep.ctx hc₀
  have hfit := hc.fit
  obtain bits : ∀ q < 256, s.mem (addr x (7168 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2) :=
    fun q hq => (h.keep.bit hc₀ q (by omega_arith)).trans (hb q hq)
  rw [combStep]
  obtain no := nib_lt S (2 * j + 1)
  obtain ne := nib_lt S (2 * j)
  -- Both digits' masks.
  refine WP.seq (WP.mono (combDigits_ok hc hj h.counter bits) fun a ⟨ka, ma⟩ => ?_)
  obtain ca := ka.keep.ctx hc
  obtain ea : env a.mem x = env s.mem x := digit_env ka.frame hfit
  obtain pa : wd a.mem x combTbl = P :=
    (wd_frame1 ka.frame hfit (by decide) (by decide) (Or.inr (by decide))).trans h.ptr
  obtain ta : TblAt x P a := ht₀.mulkeep hc₀ hts (h.keep.trans (MulKeep.of_digit hc ka))
  -- Both entries.
  refine WP.seq (WP.mono (combSelect_ok ca (mag_lt no) (mag_lt ne) ⟨ma.oddMask, ma.evenMask⟩ hj
    (ka.keep.esi.trans h.counter) pa ta) fun b ⟨bo, be, kb, fb⟩ => ?_)
  obtain cb := kb.ctx ca
  obtain eb : ∀ i : Slot, (i.val < 4 ∨ (7 ≤ i.val ∧ i.val < 13) ∨ 16 ≤ i.val) →
      env b.mem x i = env s.mem x i := fun i hi => by rw [sel_env fb hfit i hi, ea]
  obtain sb : ∀ o, 1024 ≤ o → o + 4 ≤ 8192 → wd b.mem x o = wd a.mem x o := fun o h1 h2 =>
    wd_frame fb fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_disj (by omega_arith) (by simp only [offset]; omega_arith) (Or.inr (by simp only [offset]; omega_arith))
      · exact sub_disj (by omega_arith) (by simp only [offset]; omega_arith) (Or.inr (by simp only [offset]; omega_arith))
  -- The even entry, negated for a negative digit, and added inline.
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (combNeg_ok cb 13 14 15 (by decide) (by decide) (decide (nib S (2 * j) < 8))
    (by rw [sb _ (by decide) (by decide)]; exact ma.evenSign) dis_even) fun f ⟨kf, vf⟩ => ?_
  obtain ⟨qe, hqe, hqez, hrqe⟩ := combEntry_ok j (nib S (2 * j)) hj ne
  obtain b21 : env b.mem x 21 = 0 := (eb 21 (by decide)).trans h.zero
  obtain fe' : cachedAt (env f.mem x) 13 14 15 = cache qe := by
    rw [vf, neg_env _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) b21,
      be, ← hqe]
    by_cases hlt : nib S (2 * j) < 8 <;> simp only [hlt, decide_true, decide_false, ↓reduceIte,
      Bool.false_eq_true]
  obtain ef : ∀ i : Slot, (i.val < 8 ∨ 16 ≤ i.val) → env f.mem x i = env b.mem x i := fun i hi => by
    rw [vf, neg_other _ _ _ _ _ i (fun e => by subst e; revert hi; decide)
      (fun e => by subst e; revert hi; decide) (fun e => by subst e; revert hi; decide)
      (fun e => by subst e; revert hi; decide)]
  obtain cf := kf.ctx cb
  rw [WP.block_append_iff]
  refine WP.mono (addEven_ok cf qe fe' hqez) fun g ⟨kg, gp, gh⟩ => ?_
  obtain cg := kg.ctx cf
  -- The odd entry, negated for a negative digit.
  obtain eg : ∀ i : Slot, (i.val < 8 ∨ i.val = 16 ∨ 21 ≤ i.val) → env g.mem x i = env b.mem x i :=
    fun i hi => by rw [gh i (by omega_arith), ef i (by omega_arith)]
  obtain sg : wd g.mem x combOddSign = wd b.mem x combOddSign := by
    rw [wd_frame1 kg.frame hfit (by decide) (by decide) (Or.inr (by decide)),
      wd_frame1 kf.frame hfit (by decide) (by decide) (Or.inr (by decide))]
  refine WP.mono (combNeg_ok cg 4 5 6 (by decide) (by decide) (decide (nib S (2 * j + 1) < 8))
    (by rw [sg, sb _ (by decide) (by decide)]; exact ma.oddSign) dis_odd) fun c ⟨kc, vc⟩ => ?_
  obtain ⟨qo, hqo, hqoz, hrqo⟩ := combEntry_ok j (nib S (2 * j + 1)) hj no
  obtain co : cachedAt (env c.mem x) 4 5 6 = cache qo := by
    obtain g456 : cachedAt (env g.mem x) 4 5 6 = cachedAt (env b.mem x) 4 5 6 := by
      simp only [cachedAt, eg 4 (by decide), eg 5 (by decide), eg 6 (by decide)]
    rw [vc, neg_env _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      ((eg 21 (by decide)).trans b21), g456, bo, ← hqo]
    by_cases hlt : nib S (2 * j + 1) < 8 <;> simp only [hlt, decide_true, decide_false, ↓reduceIte,
      Bool.false_eq_true]
  obtain ec : ∀ i : Slot, (i.val < 4 ∨ 9 ≤ i.val) → env c.mem x i = env g.mem x i := fun i hi => by
    rw [vc, neg_other _ _ _ _ _ i (fun e => by subst e; revert hi; decide)
      (fun e => by subst e; revert hi; decide) (fun e => by subst e; revert hi; decide)
      (fun e => by subst e; revert hi; decide)]
  obtain cc := kc.ctx cg
  -- Added by a call of `vg_ed25519_r32_add_affine`.
  obtain c4 := congrArg Spec.Ed25519.Point.X co
  obtain c5 := congrArg Spec.Ed25519.Point.Y co
  obtain c6 := congrArg Spec.Ed25519.Point.Z co
  simp only [cachedAt, cache] at c4 c5 c6
  refine WP.seq (WP.mono (affCall_ok cc qo hqoz c4 c5 c6) fun d ⟨kd, dp, dh⟩ => ?_)
  obtain d19 : d.gpr .esi = BitVec.ofNat 32 j := by
    rw [kd.keep.esi, kc.keep.esi, kg.keep.esi, kf.keep.esi, kb.esi, ka.keep.esi, h.counter]
  refine WP.mono (combNext_ok hj d19) fun t ⟨t19, t8, tedi, tesp, trd, twr, tmem⟩ => ⟨t8, ?_⟩
  obtain kdt : MulKeep x d t := ⟨tedi, tesp, trd, twr, by rw [tmem]; exact Frame.refl _ _⟩
  obtain kst : MulKeep x s t := (((((((MulKeep.of_digit hc ka).trans (MulKeep.of_sel ca kb fb)).trans
    (MulKeep.of_field cb kf)).trans (MulKeep.of_field cf kg)).trans (MulKeep.of_field cg kc)).trans
    (MulKeep.of_call cc kd)).trans kdt)
  obtain pc : point (env c.mem x) 0 1 2 3 = point (env s.mem x) 0 1 2 3 := by
    simp only [point, ec 0 (by decide), ec 1 (by decide), ec 2 (by decide), ec 3 (by decide),
      eg 0 (by decide), eg 1 (by decide), eg 2 (by decide), eg 3 (by decide),
      eb 0 (by decide), eb 1 (by decide), eb 2 (by decide), eb 3 (by decide)]
  obtain pf : point (env f.mem x) 17 18 19 20 = point (env s.mem x) 17 18 19 20 := by
    simp only [point, ef 17 (by decide), ef 18 (by decide), ef 19 (by decide), ef 20 (by decide),
      eb 17 (by decide), eb 18 (by decide), eb 19 (by decide), eb 20 (by decide)]
  obtain pd : point (env d.mem x) 17 18 19 20 = point (env g.mem x) 17 18 19 20 := by
    simp only [point, dh 17 (by decide), dh 18 (by decide), dh 19 (by decide), dh 20 (by decide),
      ec 17 (by decide), ec 18 (by decide), ec 19 (by decide), ec 20 (by decide)]
  obtain pt : wd t.mem x combTbl = P := by
    rw [tmem, wd_frame1s cc kd.frame (by decide) (by decide) (Or.inr (by decide)),
      wd_frame1 kc.frame hfit (by decide) (by decide) (Or.inr (by decide)),
      wd_frame1 kg.frame hfit (by decide) (by decide) (Or.inr (by decide)),
      wd_frame1 kf.frame hfit (by decide) (by decide) (Or.inr (by decide)),
      sb _ (by decide) (by decide)]
    exact pa
  refine ⟨by omega_arith, h.keep.trans kst, t19, pt, ?_, ?_, ?_, ?_⟩
  · rw [tmem, dh 21 (by decide), ec 21 (by decide), eg 21 (by decide)]
    exact b21
  · rw [tmem, dh 16 (by decide), ec 16 (by decide), eg 16 (by decide), eb 16 (by decide)]
    exact h.d
  · rw [tmem, dp, pc, oddSumZ, ← add_assoc, add_smul]
    exact pointAdd_rep h.odd hrqo
  · rw [tmem, pd, gp, pf, evenSumZ, ← add_assoc, add_smul]
    exact pointAdd_rep h.even hrqe

/-! ## The start and the end -/

theorem combInit_ok {s : State} {x : BitVec 32} (hc : Ctx x s) :
    WP isa (.block combInit) s fun t => MulKeep x s t ∧
      wd t.mem x combTbl = wd s.mem x combTbl ∧ env t.mem x 21 = 0 ∧
      env t.mem x 16 = env s.mem x 16 ∧
      point (env t.mem x) 0 1 2 3 = combG ∧ point (env t.mem x) 17 18 19 20 = combG ∧
      t.gpr .esi = BitVec.ofNat 32 0 := by
  rw [combInit, WP.block_append_iff]
  refine WP.mono (fieldCode_ok _ hc) fun a ⟨ka, va⟩ => ?_
  refine Wp.wp_movi fun t ht => WP.block_nil ?_
  refine ⟨(MulKeep.of_field hc ka).trans ⟨ht.other .edi (by decide), ht.other .esp (by decide), ht.rd,
      ht.wr, by rw [ht.mem]; exact Frame.refl _ _⟩,
    by rw [ht.mem]; exact wd_frame1 ka.frame hc.fit (by decide) (by decide) (Or.inr (by decide)),
    ?_, ?_, ?_, ?_, ht.gpr⟩ <;> rw [ht.mem, va] <;> rfl

theorem combFinish_ok {s : State} {x : BitVec 32} (hc : Ctx x s) {v w : ℤ}
    (hd : env s.mem x 16 = Spec.Ed25519.d)
    (ha : Rep (point (env s.mem x) 0 1 2 3) (v • baseAff))
    (hb : Rep (point (env s.mem x) 17 18 19 20) (w • baseAff)) :
    WP isa combFinish s fun t =>
      Rep (point (env t.mem x) 0 1 2 3) ((16 * v + w) • baseAff) ∧ MulKeep x s t := by
  rw [combFinish]
  refine WP.seq (WP.mono (double4_ok hc ha) fun b ⟨kb, bp, bh⟩ => ?_)
  obtain cb := kb.ctx hc
  refine WP.seq (WP.mono (fieldCode_ok [.copy 4 17, .copy 5 18, .copy 6 19, .copy 7 20] cb)
    fun c ⟨kc, vc⟩ => ?_)
  obtain cc := kc.ctx cb
  obtain cd : env c.mem x 16 = Spec.Ed25519.d := by
    rw [vc, show evalOps [.copy 4 17, .copy 5 18, .copy 6 19, .copy 7 20] (env b.mem x) 16 =
      env b.mem x 16 from rfl, bh 16 (by decide), hd]
  refine WP.mono (pointAddCall_ok cc cd) fun t ⟨kt, tp, _⟩ => ?_
  refine ⟨?_, ((MulKeep.of_ikeep hc kb).trans (MulKeep.of_field cb kc)).trans (MulKeep.of_call cc kt)⟩
  obtain p0 : point (env c.mem x) 0 1 2 3 = point (env b.mem x) 0 1 2 3 := by rw [vc]; rfl
  obtain p4 : point (env c.mem x) 4 5 6 7 = point (env s.mem x) 17 18 19 20 := by
    rw [vc]
    show point (env b.mem x) 17 18 19 20 = _
    simp only [point, bh 17 (by decide), bh 18 (by decide), bh 19 (by decide), bh 20 (by decide)]
  rw [tp, p0, p4, ← zsmul_16]
  exact pointAdd_rep bp hb

theorem combMultiply_ok {s : State} {x P : BitVec 32} (hc : Ctx x s) {S : Nat} (hS : S < 2 ^ 256)
    (hb : ∀ q < 256, s.mem (addr x (7168 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2))
    (hd : env s.mem x 16 = Spec.Ed25519.d) (hp : wd s.mem x combTbl = P) (ht : TblAt x P s)
    (hts : (TBL (P.setWidth 64)).Disjoint (callStk s)) :
    WP isa combMultiply s fun t =>
      Rep (point (env t.mem x) 0 1 2 3) (S • baseAff) ∧ MulKeep x s t := by
  rw [combMultiply]
  refine WP.seq (WP.mono (combInit_ok hc) fun b ⟨kb, bt, bz, bd, bp, bq, b19⟩ => ?_)
  obtain hg : Rep combG (((combGVal : ℤ) + 0) • baseAff) := by
    rw [add_zero, natCast_zsmul]; exact combG_ok
  obtain init : CombInv x s S P 0 b :=
    ⟨by decide, kb, b19, bt.trans hp, bz, bd.trans hd, by rw [bp]; exact hg, by rw [bq]; exact hg⟩
  obtain hl : WP isa (.loop combStep .ne) b fun t => CombInv x s S P 32 t := by
    apply WP.loop (fun n t => CombInv x s S P (32 - n) t ∧ 0 < n ∧ n ≤ 32) (n := 32)
    · intro n t ⟨hi, hn0, hn⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega_arith⟩
      refine WP.mono (combStep_ok hc hb ht hts hi (by omega_arith)) fun u ⟨u8, hu⟩ => ?_
      by_cases hk : k = 0
      · subst hk
        exact Or.inl ⟨by rw [u8]; rfl, hu⟩
      · refine Or.inr ⟨by rw [u8, show 32 - (k + 1) + 1 = 32 - k by omega_arith,
          decide_eq_false (show 32 - k ≠ 32 by omega_arith)]; rfl, k, by omega_arith, ?_, by omega_arith, by omega_arith⟩
        rw [show 32 - k = 32 - (k + 1) + 1 by omega_arith]; exact hu
    · exact ⟨init, by decide, by decide⟩
  refine WP.seq (WP.mono hl fun t hi => ?_)
  refine WP.mono (combFinish_ok (hi.keep.ctx hc) hi.d hi.odd hi.even) fun u ⟨hu, ku⟩ =>
    ⟨?_, hi.keep.trans ku⟩
  rw [comb_total hS, natCast_zsmul] at hu
  exact hu

end VG.Proof.Ed25519.X86

end

end

/-! ### `Ed25519.X86.CombCT`, which this module and modules that import it used -/

section

/-! The comb has a public trace: its loops' counters (`esi`) are public, and every address is
the workspace pointer `edi` plus a constant or `8 esi`, or the tables' address plus
`768 esi` and a constant. The tables' address is the word at byte `combTbl` of the workspace,
which the comb never writes, public (`callTaint combTbl`): the digits only reach masks. The
calls of `vg_ed25519_r32_add_affine` and of `_point_add` are analysed by their summaries, and
those of `_double`, after the loop, as part of the comb. -/

@[expose] public section

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86

theorem combMultiply_ct {x : BitVec 32} : RelCT isa
    (fun s t => PointCTCtx x s ∧ PointCTCtx x t ∧ s.wr = t.wr ∧ s.gpr .esp = t.gpr .esp ∧
      wd s.mem x combTbl = wd t.mem x combTbl) combMultiply (fun _ _ => True) := by
  obtain ⟨_, hc⟩ : ∃ h, (taint.check (callTaint combTbl) combMultiply h).isSome = true := by
    native_taint_decide_sum [affSum, addSum]
  apply VG.RelCT.taint (A := taint) (callTaint combTbl) _ hc
  intro s t ⟨hs, ht, hw, hsp, hv⟩
  exact callTaint_agree hs ht hw hsp (by decide) hv

end VG.Proof.Ed25519.X86

end

end

/-! ### `Ed25519.X86.ScalarBaseCTSetup`, which only this module used -/

section

/-! ### `Ed25519.X86.PointCTMul`, which only this module used -/

section

/-! Merged from `Proof.Ed25519.X86.PointCTBatch`. -/

@[expose] public section

/-! Merged from `Proof.Ed25519.X86.PointCTMulLoop`. -/

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

structure MulCTInput (x : BitVec 32) (scalar count : Nat) (s : State) : Prop where
  ctx : PointCTCtx x s
  bound : scalar < 2 ^ (16 * count)
  bits : ∀ i < 16 * count, s.mem (addr x (7168 + i)) = BitVec.ofNat 8 (scalarBit scalar i).toNat
  d : env s.mem x 16 = Spec.Ed25519.d

end VG.Proof.Ed25519.X86

end

end

@[expose] public section

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def baseScalar (s : State) : Nat := Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32)

theorem pointCTCtx_saved {s₀ s : State} (h : BaseRegions s₀) (hs : Saved s₀ (arg s₀ 2) s) :
    PointCTCtx (arg s₀ 2) s := by
  obtain ⟨hp, _, ho⟩ := scalarBase_pre h
  refine ⟨hs.ctx hp.fit hp.wr hp.stk, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs.wr, h.2.1]
    exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)
  · rw [hs.wr, h.2.1]
    exact List.pairwise_cons.mpr ⟨by simpa using ho.sep, by simp⟩
  · intro r hr
    rw [hs.wr, h.2.1] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [BitVec.toNat_setWidth]
    · omega_using [ho.fit]
    · omega_using [hp.fit]
  · change s.wr.getD 1 ⟨0, 0⟩ = _
    rw [hs.wr, h.2.1]; rfl
  · intro r hr
    rw [hs.wr, h.2.1] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [callStk, hs.esp]
    rcases hr with rfl | rfl
    · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- After the body's start: the callee-saved registers saved, the scalar's bits, `d`, and the
tables' address and the tables, apart from the stack a call uses. -/
def BaseCTReady (s₀ s : State) : Prop :=
  Saved s₀ (arg s₀ 2) s ∧ MulCTInput (arg s₀ 2) (baseScalar s₀) 16 s ∧
    wd s.mem (arg s₀ 2) combTbl = s₀.syms combSym ∧ TblAt (arg s₀ 2) (s₀.syms combSym) s ∧
    (TBL ((s₀.syms combSym).setWidth 64)).Disjoint (callStk s)

theorem scalarBaseStart_ok {s : State} (h : BodyPre s) :
    WP isa scalarBaseStart s (BaseCTReady s) := by
  obtain ⟨hr, hptr, htbl, hts⟩ := h
  obtain ⟨hp, hi, _⟩ := scalarBase_pre hr
  have scalar_bound : baseScalar s < 2 ^ (16 * 16) := by
    have hb := decodeLE_lt (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32)
    simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range] at hb
    change baseScalar s < 256 ^ 32 at hb
    rw [show 2 ^ (16 * 16) = 256 ^ 32 by decide]
    exact hb
  rw [scalarBaseStart]
  refine WP.seq (WP.mono (abiSave_frame hp) fun a ⟨ha, fa⟩ => ?_)
  refine WP.seq (WP.mono (inputBits_frame hp hi ha (by decide) (by decide) (by decide))
    fun b ⟨hb, fb, bits⟩ => ?_)
  have cb := hb.ctx hp.fit hp.wr hp.stk
  refine WP.mono (fieldCode_ok baseSetupOps cb) fun c ⟨kc, ec⟩ => ?_
  have hc := hb.ikeep hp.fit (IKeep.of_field kc)
  have toScr : ∀ {m m' : Mem} {o n : Nat}, Frame [sub (arg s 2) o n] m m' → o + n ≤ 8192 → o < 8192 →
      Frame [scR 8192 (arg s 2)] m m' := fun f h1 h2 => f.sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨_, List.mem_singleton_self _, by rw [scR_eq]; exact sub_sub hp.fit (Nat.zero_le _) h1 h2⟩
  refine ⟨hc, ⟨pointCTCtx_saved hr hc, scalar_bound, ?_, ?_⟩, ?_,
    htbl.of_frame hc.rd (((toScr fa (by decide) (by decide)).trans (toScr fb (by decide) (by decide))).trans
      (toScr kc.frame (by decide) (by decide))) fun r hr => by
        rw [List.mem_singleton.mp hr]; exact fun _ h => h, by rw [callStk, hc.esp]; exact hts⟩
  · intro i ii
    rw [IKeep.bit (IKeep.of_field kc) cb i (by omega_using [ii]), bits i (by omega_using [ii]), scalarBit_nat]
    rfl
  · rw [ec, baseSetup_d]
  · rw [wd_frame1 kc.frame hp.fit (by decide) (by decide) (Or.inr (by decide)),
      wd_frame1 fb hp.fit (by decide) (by decide) (Or.inl (by decide)),
      wd_frame1 fa hp.fit (by decide) (by decide) (Or.inr (by decide))]
    exact hptr


theorem scalarBaseStart_ct : RelCT isa
    (fun s t => BodyPre s ∧ BodyPre t ∧ scalarBaseLocal.pub s t)
    scalarBaseStart (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (scalarTaint 2 3) _ (by native_taint_decide)
  intro s t ⟨hs, ht, hp⟩
  obtain ⟨sp, a0, a1, a2, _⟩ := hp
  obtain ⟨ps, _, os⟩ := scalarBase_pre hs.1
  obtain ⟨pt, _, ot⟩ := scalarBase_pre ht.1
  refine scalarTaint_agree (scalarTaint_wf ps os hs.1.2.1 hs.1.2.2.2.2.1)
    (scalarTaint_wf pt ot ht.1.2.1 ht.1.2.2.2.2.1) sp ?_ (by decide) hs.1.2.1 ht.1.2.1 ps.sp_fit pt.sp_fit
  intro i hi
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  exacts [a0, a1, a2]

/-- The prologue's trace: the frame's word below `esp`, the argument and the store, all at
public addresses. -/
theorem combAddr_ct : RelCT isa
    (fun s t => scalarBaseLocal.pre s ∧ scalarBaseLocal.pre t ∧ scalarBaseLocal.pub s t)
    (combAddr 2) (fun _ _ => True) := by
  unfold combAddr
  have fr : RelCT isa
      (fun s t => scalarBaseLocal.pre s ∧ scalarBaseLocal.pre t ∧ scalarBaseLocal.pub s t)
      (.frame (.symPush .eax combSym) (.block []) (.pop .ecx 1)) (fun _ _ => True) := by
    intro s t tr₁ tr₂ s' t' h e₁ e₂
    exact ⟨by rw [symFrame_trace h.1.1.sp4 e₁, symFrame_trace h.2.1.1.sp4 e₂, h.2.2.1], trivial⟩
  have pre := fr.wpDep (F := fun s t => SymAddrPost combSym s t) (fun s t h =>
    ⟨symFrame_ok combSym s h.1.1.sp4, symFrame_ok combSym t h.2.1.1.sp4⟩)
  refine pre.seq ?_
  apply VG.RelCT.taint (A := taint) (scalarTaint 2 3) _ (by native_taint_decide)
  intro s t ⟨_, a, b, ⟨ha, hb, hp⟩, P, Q⟩
  have hs := ha.1.symAddr P ha.1.sp4
  have ht := hb.1.symAddr Q hb.1.sp4
  obtain ⟨ps, _, os⟩ := scalarBase_pre hs
  obtain ⟨pt, _, ot⟩ := scalarBase_pre ht
  have fa : (a.gpr .esp).toNat + 16 ≤ 2 ^ 32 := ha.1.spfit
  have fb : (b.gpr .esp).toNat + 16 ≤ 2 ^ 32 := hb.1.spfit
  refine scalarTaint_agree (scalarTaint_wf ps os hs.2.1 hs.2.2.2.2.1)
    (scalarTaint_wf pt ot ht.2.1 ht.2.2.2.2.1) ?_ ?_ (by decide) hs.2.1 ht.2.1 ps.sp_fit pt.sp_fit
  · rw [P.gpr .esp (by decide), Q.gpr .esp (by decide), hp.1]
  · intro i hi
    rw [P.arg ha.1.sp4 (by omega_using [fa, hi]), Q.arg hb.1.sp4 (by omega_using [fb, hi])]
    obtain ⟨_, a0, a1, a2, _⟩ := hp
    rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    exacts [a0, a1, a2]

end VG.Proof.Ed25519.X86

end

end

/-! Merged from `Proof.Ed25519.X86.ScalarBaseCT`. -/

@[expose] public section

section
/-! Merged from `Proof.Ed25519.X86.ScalarBaseCTFinish`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def BaseSaved (s₀ t₀ s t : State) : Prop := Saved s₀ (arg s₀ 2) s ∧ Saved t₀ (arg t₀ 2) t

theorem scalarBaseFinish_ct (s₀ t₀ : State) (hs : BaseRegions s₀) (ht : BaseRegions t₀)
    (hp : scalarBaseLocal.pub s₀ t₀) : RelCT isa (BaseSaved s₀ t₀) (.block (finishWords 96)) (fun _ _ => True) := by
  obtain ⟨ps, _, _⟩ := scalarBase_pre hs
  obtain ⟨pt, _, _⟩ := scalarBase_pre ht
  have loadct : RelCT isa (BaseSaved s₀ t₀)
      (.block [.mov .esi (.mem (Impl.X25519.X86.at_ .esp 4))]) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.esp]) _ (by native_taint_decide)
    intro s t h
    exact regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸
      (h.1.esp.trans (hp.1.trans h.2.esp.symm)))
  have hh := ctWithRuns loadct (fun _ _ h => ⟨loadArg_ok (i := 0) ps h.1 (by decide),
    loadArg_ok (i := 0) pt h.2 (by decide)⟩)
  have tailct : RelCT isa (fun s t => s.gpr .edi = t.gpr .edi ∧ s.gpr .esi = t.gpr .esi)
      (.block (outputWords 96 8 ++ Impl.X25519.X86.restore)) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi, .esi]) _ (by native_taint_decide)
    intro s t h
    apply regsTaint_agree
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h.1, h.2]
  simp only [finishWords, List.append_assoc]
  refine ctBlockAppend (hh.mono (fun _ _ h => h) ?_) tailct
  intro s t ⟨_, a, b, _, ha, hb⟩
  exact ⟨ha.1.edi.trans (hp.2.2.2.1.trans hb.1.edi.symm), ha.2.1.trans (hp.2.1.trans hb.2.1.symm)⟩

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem scalarBaseTail_ct (s₀ t₀ : State) (hs : BaseRegions s₀) (ht : BaseRegions t₀)
    (hp : scalarBaseLocal.pub s₀ t₀) :
    RelCT isa (fun s t => BaseCTReady s₀ s ∧ BaseCTReady t₀ t)
      (.seq combMultiply (.seq pointEncode (.block (finishWords 96)))) (fun _ _ => True) := by
  have mulct := (combMultiply_ct (x := arg s₀ 2)).mono
    (P' := fun (s t : State) => BaseCTReady s₀ s ∧ BaseCTReady t₀ t)
    (fun s t h => by
      have ht' := h.2.2.1.ctx
      rw [← hp.2.2.2.1] at ht'
      refine ⟨h.1.2.1.ctx, ht', ?_, ?_, ?_⟩
      · rw [h.1.1.wr, h.2.1.wr, hs.2.1, ht.2.1, hp.2.1, hp.2.2.2.1]
      · rw [h.1.1.esp, h.2.1.esp, hp.1]
      · rw [h.1.2.2.1, hp.2.2.2.1, h.2.2.2.1, hp.2.2.2.2]) (fun _ _ h => h)
  have mw (u s : State) (h : BaseCTReady u s) : WP isa combMultiply s (Saved u (arg u 2)) := by
    refine WP.mono (combMultiply_ok (S := baseScalar u) h.2.1.ctx.ctx (by simpa using h.2.1.bound)
      (fun q hq => by rw [h.2.1.bits q (by omega_using [hq]), scalarBit_nat]) h.2.1.d h.2.2.1 h.2.2.2.1 h.2.2.2.2)
      fun t ⟨_, kt⟩ => ?_
    exact h.1.mulkeep h.2.1.ctx.ctx.fit kt
  have mul := ctWithRuns mulct (fun s t h => ⟨mw s₀ s h.1, mw t₀ t h.2⟩)
  have encct := (pointEncode_ct (x := arg s₀ 2)).mono (P' := BaseSaved s₀ t₀)
    (fun _ _ h => by
      have ct := pointCTCtx_saved ht h.2
      rw [← hp.2.2.2.1] at ct
      exact ⟨pointCTCtx_saved hs h.1, ct, by rw [h.1.wr, h.2.wr, hs.2.1, ht.2.1, hp.2.1, hp.2.2.2.1],
        by rw [h.1.esp, h.2.esp, hp.1]⟩) (fun _ _ h => h)
  have ew (u s : State) (hu : BaseRegions u) (h : Saved u (arg u 2) s) :
      WP isa pointEncode s (Saved u (arg u 2)) := by
    have pu := (scalarBase_pre hu).1
    refine WP.mono (pointEncode_ok (h.ctx pu.fit pu.wr pu.stk)) fun t ⟨kt, _⟩ => ?_
    exact h.ikeep pu.fit kt
  have enc := ctWithRuns encct (fun s t h => ⟨ew s₀ s hs h.1, ew t₀ t ht h.2⟩)
  refine VG.RelCT.seq (mul.mono (fun _ _ h => h) (fun _ _ ⟨_, _, _, _, ha, hb⟩ => ⟨ha, hb⟩))
    (VG.RelCT.seq (enc.mono (fun _ _ h => h) (fun _ _ ⟨_, _, _, _, ha, hb⟩ => ⟨ha, hb⟩))
      (scalarBaseFinish_ct s₀ t₀ hs ht hp))

theorem scalarBaseBody_ct : RelCT isa (fun s t => BodyPre s ∧ BodyPre t ∧ scalarBaseLocal.pub s t)
    scalarBaseBody (fun _ _ => True) := by
  have start := ctWithRuns scalarBaseStart_ct
    (fun _ _ h => ⟨scalarBaseStart_ok h.1, scalarBaseStart_ok h.2.1⟩)
  rw [scalarBaseBody]
  refine VG.RelCT.seq start ?_
  intro s t ts tt s' t' ⟨_, u, v, hp, hu, hv⟩ es et
  exact scalarBaseTail_ct u v hp.1.1 hp.2.1.1 hp.2.2 _ _ _ _ _ _ ⟨hu, hv⟩ es et

theorem scalarBase_ct : ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub scalarBase := by
  apply VG.RelCT.constantTime (Q := fun _ _ => True)
  have pro := ctWithRuns combAddr_ct (fun _ _ h => ⟨combAddr_ok h.1, combAddr_ok h.2.1⟩)
  rw [scalarBase]
  refine VG.RelCT.seq pro ?_
  intro s t ts tt s' t' ⟨_, u, v, ⟨_, _, hp⟩, Pu, Pv⟩ es et
  exact scalarBaseBody_ct _ _ _ _ _ _ ⟨Pu.pre, Pv.pre, Prologue.pub Pu Pv hp⟩ es et

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem scalarBaseBody_correct {s : State} (h : BodyPre s) :
    WP isa scalarBaseBody s fun t => abiPreserved s t ∧ scalarBaseLocal.post s t := by
  obtain ⟨hp, _, ho⟩ := scalarBase_pre h.1
  rw [scalarBaseBody]
  refine WP.seq (WP.mono (scalarBaseStart_ok h) fun c ⟨hc, mc, pc, tc⟩ => ?_)
  refine WP.seq (WP.mono (combMultiply_ok (S := baseScalar s) mc.ctx.ctx (by simpa using mc.bound)
    (fun q hq => by rw [mc.bits q (by omega_using [hq]), scalarBit_nat]) mc.d pc tc.1 tc.2) fun d ⟨pd, kd⟩ => ?_)
  have hd := hc.mulkeep hp.fit kd
  refine WP.seq (WP.mono (pointEncode_value (hd.ctx hp.fit hp.wr hp.stk)) fun e ⟨ke, ve⟩ => ?_)
  have he := hd.ikeep hp.fit ke
  refine WP.mono (finishWords_ok hp ho he (src := 96) (by decide)) fun t ⟨abi_t, et⟩ => ⟨abi_t, ?_⟩
  change Spec.Ed25519.bytesAt t.mem ((arg s 0).setWidth 64) 32 = _
  rw [et, ve, encodePoint_rep pd, Spec.Ed25519.scalarBase,
    encodePoint_rep (pointMul_rep _ basePoint_rep)]
  rfl

theorem scalarBase_correct {s : State} (h : scalarBaseLocal.pre s) :
    WP isa scalarBase s fun t => abiPreserved s t ∧ scalarBaseLocal.post s t := by
  rw [scalarBase]
  refine WP.seq (WP.mono (combAddr_ok h) fun s₁ P => ?_)
  refine WP.mono (scalarBaseBody_correct P.pre) fun t ⟨ha, hq⟩ => ⟨P.abi ha, ?_⟩
  change Spec.Ed25519.bytesAt t.mem ((arg s₁ 0).setWidth 64) 32 =
    Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt s₁.mem ((arg s₁ 1).setWidth 64) 32) at hq
  change Spec.Ed25519.bytesAt t.mem ((arg s 0).setWidth 64) 32 =
    Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32)
  rw [P.args 0 (by decide), P.args 1 (by decide), P.input] at hq
  exact hq

theorem scalarBase_ok (s : State) (h : scalarBaseLocal.pre s) :
    ∃ tr t, Exec isa scalarBase s tr t ∧ abiPreserved s t ∧ scalarBaseLocal.post s t :=
  scalarBase_correct h

/-- The `n` bytes below `sp`, as the contract states them. -/
theorem below_eq {sp : BitVec 32} {n : Nat} (h : n ≤ sp.toNat) :
    below sp n = ⟨sp.setWidth 64 - BitVec.ofNat 64 n, n⟩ := by
  simp only [below, Taint.sub_setWidth h]

end VG.Proof.Ed25519.X86

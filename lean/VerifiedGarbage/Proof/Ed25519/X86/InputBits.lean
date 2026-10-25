module

public import VerifiedGarbage.Impl.Ed25519.X86.InputBits
public import VerifiedGarbage.Proof.Ed25519.X86.CommonInput
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Ed25519.X86.CommonMemory
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub

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

theorem inputBits_ok {s₀ s : State} {scidx argc i n : Nat}
    (hp : ScratchPre s₀ scidx argc) (hi : InputPre s₀ scidx i n)
    (hs : Saved s₀ (arg s₀ scidx) s) (hia : i < argc) (hn : n ≤ 16) (hn1 : 1 ≤ n) :
    WP isa (inputBits i (4 * n)) s fun t => Saved s₀ (arg s₀ scidx) t ∧
      (∀ k < 32 * n, t.mem (addr (arg s₀ scidx) (7168 + k)) = BitVec.ofNat 8
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ i).setWidth 64) (4 * n)) / 2 ^ k % 2)) :=
  WP.mono (inputBits_frame hp hi hs hia hn hn1) fun _ h => ⟨h.1, h.2.2⟩

end VG.Proof.Ed25519.X86

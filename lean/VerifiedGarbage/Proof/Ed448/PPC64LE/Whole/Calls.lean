module

import VerifiedGarbage.Proof.Ed448.PPC64LE.BaseVerified
public import VerifiedGarbage.Proof.X448.PPC64LE.Slots
import VerifiedGarbage.Proof.X448.PPC64LE.Freeze
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.Ed448.Binary
public import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.X448.PPC64LE.Field
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.Ed448.PPC64LE.Scalar
public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Ed448.PPC64LE.VVerified
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Ed448.PPC64LE.BaseMain
public import VerifiedGarbage.Proof.Ed448.PPC64LE.ScalarBit
import VerifiedGarbage.Proof.X25519.PPC64LE.Pass
import VerifiedGarbage.Proof.X25519.PPC64LE.Mul
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.WriteBytes

/-! ### `Ed448.PPC64LE.ScalarReduce`, which only this module used -/

section

/-! ### `Ed448.PPC64LE.Pack`, which this module and modules that import it used -/

section

/-!
# Ed448 on PPC64LE: remainders to memory outside the working space

`packWords a n` copies the `n` words at `a` of the working space to the
bytes at `r14` (`packWords_ok`), and `packScalar a` the remainder at `a` as
57 bytes: its fourteen words and a zero byte, the encoding of a number below
`2⁴⁴⁸` (`packScalar_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE VG.Proof.X448.PPC64LE
open VG.Proof.X25519.PPC64LE hiding V FS V_lt pass_ok limb_frame

/-- After `k` words of `packWords a n` from `s0`. -/
structure PackInv (b q : Addr) (a : Nat) (s0 : State) (k : Nat) (s : State) : Prop where
  rest : Rest [.r7] s0 s
  frame : Frame [⟨q, 4 * k⟩] s0.mem s.mem
  outs : ∀ j < k, wd s.mem q (4 * j) = limb s0.mem b a j

theorem packWords_ok {b q : Addr} {s0 : State} (hc : Ctx b s0) (h14 : s0.gpr .r14 = q) {a n : Nat}
    (ha : a + 4 * n ≤ 4096) (hn : 4 * n < 2 ^ 15)
    (hw : ∀ k < n, InRegions s0.wr (q + BitVec.ofNat 64 (4 * k)) 4)
    (hd : (⟨q, 4 * n⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 a, 4 * n⟩) :
    WP isa (.block (packWords a n)) s0 (PackInv b q a s0 n) := by
  refine wp_range_flatMap (M := isa) (PackInv b q a s0) (fun k s hk h => ?_)
    n (Nat.le_refl _) s0 ⟨Rest.refl _ _, Frame.refl _ _, fun j hj => by omega⟩
  have hcs : Ctx b s := hc.of_rest h.rest (by decide)
  unfold packStep
  refine lw0_ok hcs (d := a + 4 * k) (by omega_using [ha, hk]) fun t1 v1 => ?_
  refine wp_sw (a := q + BitVec.ofNat 64 (4 * k)) (by decide) (by omega_using [ha, hk])
    (by rw [v1.other _ (by decide), h.rest.gpr _ (by decide), h14])
    (by rw [v1.wr, h.rest.wr]; exact hw k hk) fun t2 v2 => WP.block_nil ?_
  have em : t2.mem = s.mem.writeW (q + BitVec.ofNat 64 (4 * k)) ((t1.gpr .r7).setWidth 32) := by
    rw [v2.mem, v1.mem]
  have hsrc : wd s.mem b (a + 4 * k) = limb s0.mem b a k := by
    refine wd_frame h.frame fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    refine fun x hx hx' => hd x ?_ ?_
    · exact Region.sub_prefix (by omega_using [hk]) x hx'
    · exact Offset.sub b (d := a + 4 * k) (n := 4) (e := a) (k := 4 * n) (by omega_using []) (by omega_using [hk]) x hx
  refine ⟨h.rest.trans ((v1.rest (by decide)).trans (v2.rest _)), ?_, fun j hj => ?_⟩
  · rw [em]
    refine (h.frame.sub fun r hmem => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using []) (by omega_using [ha, hk]))
    rw [List.mem_singleton.mp hmem]
    exact Region.sub_prefix (by omega_using [])
  · rw [em]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega_using [hj]) (by omega_arith) (by omega_using [ha, hk])]
      exact h.outs j hj
    · rw [wd_write_self, toNat_lo32, v1.gpr, toNat_ext32, Nat.mod_eq_of_lt (BitVec.isLt _)]
      exact hsrc

theorem pow448_256 : (256 : Nat) ^ 56 = 2 ^ 224 * 2 ^ 224 := by decide +kernel

/-- The 57 bytes of a number below `2⁴⁴⁸`: its 56 bytes and a zero byte. -/
theorem encodeLE_57_zero {x : Nat} (hx : x < 2 ^ 224 * 2 ^ 224) :
    Spec.Ed448.encodeLE 57 x = Proof.X25519.leBytes 56 x ++ [0] := by
  rw [Proof.Ed448.encodeLE_eq, show 57 = 56 + 1 from rfl, Proof.X25519.leBytes_add, Proof.Ed448.leBytes_one,
    Nat.div_eq_of_lt (by rw [pow448_256]; exact hx)]
  rfl

/-- **The remainder at `a`** as the 57 bytes at `r14`. -/
theorem packScalar_ok {b q : Addr} {s0 : State} (hc : Ctx b s0) (h14 : s0.gpr .r14 = q) {a : Nat}
    (ha : a + 56 ≤ 4096) (hw : (⟨q, 57⟩ : Region) ∈ s0.wr)
    (hd : (⟨q, 57⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 a, 56⟩) :
    WP isa (.block (packScalar a)) s0 fun t =>
      Rest [.r7] s0 t ∧ Frame [⟨q, 57⟩] s0.mem t.mem ∧
      Spec.Ed448.bytesAt t.mem q 57 = Spec.Ed448.encodeLE 57 (V s0.mem b a) := by
  unfold packScalar
  refine WP.append (packWords_ok hc h14 (n := 14) (by omega_using [ha]) (by decide)
    (fun k hk => in_base hw (by omega_using [hk]) (by omega_using [hk]))
    (hd.sub_left (Region.sub_prefix (by decide)))) fun s1 h1 => ?_
  refine wp_li (by decide) fun s2 u2 => ?_
  refine wp_stb (a := q + BitVec.ofNat 64 56) (by decide) (by decide)
    (by rw [u2.other _ (by decide), h1.rest.gpr _ (by decide), h14])
    (by rw [u2.wr, h1.rest.wr]; exact in_base hw (by decide) (by decide)) fun s3 u3 => WP.block_nil ?_
  have hm3 : s3.mem = s1.mem.writeW (q + BitVec.ofNat 64 56) (0 : BitVec 8) := by
    rw [u3.mem, u2.gpr, u2.mem]; rfl
  refine ⟨h1.rest.trans ((u2.rest (by decide)).trans (u3.rest _)), ?_, ?_⟩
  · rw [hm3]
    exact (h1.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (n := 8 / 8) (by decide) (by decide))
  · have hlt := V_lt s0.mem b a
    rw [encodeLE_57_zero hlt, show (57 : Nat) = 56 + 1 from rfl, Proof.Ed448.bytesAt_eq,
      Proof.X25519.bytesAt_add, ← Proof.Ed448.bytesAt_eq]
    congr 1
    · have f3 : Frame [⟨q + BitVec.ofNat 64 56, 1⟩] s1.mem s3.mem := by
        rw [hm3]
        exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
          (Region.contains_self _ (8 / 8))
      have e : ∀ j < 14, wd s3.mem q (4 * j) = limb s0.mem b a j := fun j hj => by
        rw [wd_frame f3 fun r hr => by
          rw [List.mem_singleton.mp hr]
          exact Offset.disjoint q (d := 4 * j) (n := 4) (e := 56) (k := 1) (.inl (by omega_using [hj])) (by omega_using [hj]) (by omega_using [])]
        exact h1.outs j hj
      exact bytesAt_words14 _ _ e
    · show [s3.mem (q + BitVec.ofNat 64 56 + BitVec.ofNat 64 0)] = [0]
      rw [hm3, VG.WriteBytes.writeW8_apply]
      exact congrArg (· :: []) (ite_eq_left (by simp))

end VG.Proof.Ed448.PPC64LE

end

end

/-! ### `Ed448.PPC64LE.ScalarLoop`, which this module and modules that import it used -/

section

/-!
# Ed448 on PPC64LE: an integer of `N` bytes modulo `L`

`scalarEngine o N` reads the `N` bytes at `r14` from the top, each into the
remainder at `o` bit by bit (`scalarByte_ok`), and leaves the integer modulo
`L` there (`engine_ok`), for bytes that the remainder and its candidate at
`SD` do not overlap.
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE VG.Proof.X448.PPC64LE
open VG.Proof.X25519.PPC64LE hiding V FS V_lt pass_ok limb_frame
open VG.Spec.Ed448 (L decodeLE bytesAt)

/-- Bit `j` of a byte, as `consumeBits` takes it. -/
theorem bit_toNat {w : Nat} (hw : w < 256) (j : Nat) :
    ((BitVec.ofNat 64 w).getLsbD j).toNat = w / 2 ^ j % 2 := by
  rw [BitVec.getLsbD_ofNat]
  by_cases hj : j < 64
  · simp only [hj, decide_true, Bool.true_and, Nat.testBit, Nat.shiftRight_eq_div_pow]
    cases h : w / 2 ^ j % 2 == 1 <;> simp_all <;> omega
  · simp only [hj, decide_false, Bool.false_and, Bool.toNat_false]
    rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide : 2 > 0) (by omega_using [hj] : 8 ≤ j)))]

/-- What the scalar code writes: the remainder at `o` and its candidate. -/
abbrev RD (b : Addr) (o : Nat) : List Region := [⟨b + BitVec.ofNat 64 o, 56⟩, ⟨b + BitVec.ofNat 64 SD, 56⟩]

section
variable {b : Addr}

/-- The bits `js` of the byte in `r16`, in turn. -/
theorem scalarBits_ok {o : Nat} (ho : Rem o) {w : Nat} (hw : w < 256) :
    ∀ (js : List Nat), (∀ j ∈ js, j < 8) → ∀ {s : State}, Ctx b s → (s.gpr .r16).toNat = w →
      V s.mem b o < L →
      WP isa (.block (js.flatMap (scalarBit o))) s fun t =>
        Rest [.r5, .r7, .r8, .r11] s t ∧ Frame (RD b o) s.mem t.mem ∧
        V t.mem b o = js.foldl (fun v j => (2 * v + w / 2 ^ j % 2) % L) (V s.mem b o)
  | [], _, _, _, _, _ => WP.block_nil ⟨Rest.refl _ _, Frame.refl _ _, List.foldl_nil.symm⟩
  | j :: js, hj, s, hc, h16, hr => by
    rw [List.flatMap_cons]
    refine WP.append (scalarBit_ok ho hc hw (hj j List.mem_cons_self) h16 hr) fun t ⟨rt, ft, vt⟩ => ?_
    refine WP.mono (scalarBits_ok ho hw js (fun j h => hj j (List.mem_cons_of_mem _ h))
      (hc.of_rest rt (by decide)) (by rw [rt.gpr _ (by decide), h16])
      (by rw [vt]; exact Nat.mod_lt _ Proof.Ed448.order_pos))
      fun u ⟨ru, fu, vu⟩ => ⟨rt.trans ru, ft.trans fu, by rw [vu, vt]; rfl⟩

/-- One byte: `r15` counted down, the byte at `r14 + r15` into the remainder. -/
theorem scalarByte_ok {o : Nat} (ho : Rem o) {s : State} (hc : Ctx b s) {p : Addr} (h14 : s.gpr .r14 = p)
    {n : Nat} (hn : n + 1 < 2 ^ 15) (h15 : s.gpr .r15 = BitVec.ofNat 64 (n + 1))
    (hin : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 n) 1) (hr : V s.mem b o < L) :
    WP isa (.block (scalarByte o)) s fun t =>
      Rest [.r5, .r7, .r8, .r11, .r15, .r16] s t ∧ Frame (RD b o) s.mem t.mem ∧
      t.gpr .r15 = BitVec.ofNat 64 n ∧
      V t.mem b o = (256 * V s.mem b o + (s.mem (p + BitVec.ofNat 64 n)).toNat) % L := by
  unfold scalarByte scalarRead
  simp only [List.cons_append, List.nil_append]
  refine wp_subi (by decide) (by decide) fun s1 u1 => wp_add fun s2 u2 => ?_
  have e15 : s1.gpr .r15 = BitVec.ofNat 64 n := by
    rw [u1.gpr, h15, ofNat_sub_one (by omega_using []) (by omega_using [hn]), Nat.add_sub_cancel]
  refine wp_lbz (a := p + BitVec.ofNat 64 n) (by decide) (by decide)
    (by rw [BitVec.add_zero, u2.gpr, u1.other .r14 (by decide), h14, e15])
    (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact hin) fun s3 u3 => ?_
  have hr3 : Rest [.r7, .r15, .r16] s s3 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))
  have hm3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  have hw := (s.mem (p + BitVec.ofNat 64 n)).isLt
  have h16 : (s3.gpr .r16).toNat = (s.mem (p + BitVec.ofNat 64 n)).toNat := by
    rw [u3.gpr, u2.mem, u1.mem, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [])]
  refine WP.mono (scalarBits_ok ho hw _ (fun j hj => by simpa using hj) (hc.of_rest hr3 (by decide)) h16
    (by rw [hm3]; exact hr)) fun t ⟨rt, ft, vt⟩ => ⟨(hr3.mono (by decide)).trans (rt.mono (by decide)),
      by rw [hm3] at ft; exact ft, by rw [rt.gpr _ (by decide), u3.other _ (by decide), u2.other _ (by decide), e15], ?_⟩
  rw [vt, hm3]
  obtain ⟨w, hw'⟩ : ∃ w, w = (s.mem (p + BitVec.ofNat 64 n)).toNat := ⟨_, rfl⟩
  rw [← hw'] at hw ⊢
  have e : (fun v j => (2 * v + w / 2 ^ j % 2) % L) =
      fun v j => (2 * v + ((BitVec.ofNat 64 w).getLsbD j).toNat) % L :=
    funext fun v => funext fun j => by rw [bit_toNat hw j]
  rw [e]
  have hc8 := Proof.Ed448.consumeBits_eq (BitVec.ofNat 64 w) 8 (V s.mem b o) hr
  have hw64 : (BitVec.ofNat 64 w).toNat = w := by rw [BitVec.toNat_ofNat]; omega_using [hw]
  rw [hw64, Nat.mod_eq_of_lt (show w < 2 ^ 8 by omega_using [hw]), show (2 : Nat) ^ 8 = 256 from rfl] at hc8
  unfold Proof.Ed448.consumeBits at hc8
  exact hc8

theorem bytesAt_drop (m : Mem) (p : Addr) {N n : Nat} (hn : n < N) :
    (bytesAt m p N).drop n = m (p + BitVec.ofNat 64 n) :: (bytesAt m p N).drop (n + 1) := by
  rw [List.drop_eq_getElem_cons (by simp [bytesAt]; omega_using [hn])]
  simp [bytesAt]

/-- After the bytes from `n` up: the remainder of the integer they make. -/
structure EngInv (b p : Addr) (o N : Nat) (s0 : State) (n : Nat) (t : State) : Prop where
  le : n ≤ N
  pos : 1 ≤ n
  rest : Rest [.r5, .r7, .r8, .r11, .r15, .r16] s0 t
  frame : Frame (RD b o) s0.mem t.mem
  r15 : t.gpr .r15 = BitVec.ofNat 64 n
  val : V t.mem b o = decodeLE ((bytesAt s0.mem p N).drop n) % L

/-- **The `N` bytes at `r14`**, modulo `L`, into the remainder at `o`. -/
theorem engine_ok {o : Nat} (ho : Rem o) {N : Nat} (hN : 1 ≤ N) (hN' : N < 2 ^ 15) {s : State} (hc : Ctx b s)
    {p : Addr} (h14 : s.gpr .r14 = p)
    (hin : ∀ i < N, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 i) 1)
    (hd : ∀ i < N, ∀ r ∈ RD b o, ¬ r.Contains (p + BitVec.ofNat 64 i) 1) :
    WP isa (scalarEngine o N) s fun t =>
      Rest [.r5, .r7, .r8, .r11, .r15, .r16] s t ∧ Frame (RD b o) s.mem t.mem ∧
      V t.mem b o = decodeLE (bytesAt s.mem p N) % L := by
  have hf := ho.fits
  unfold scalarEngine
  rw [List.cons_append]
  refine WP.seq (wp_li (by decide) fun s0 u0 => ?_)
  have hc0 : Ctx b s0 := hc.of_rest (u0.rest (ws := [.r7]) (by decide)) (by decide)
  refine WP.append (stores_ok (r := .r7) (o := o) (n := 14) (by omega_using [hf]) hc0) fun s1 ⟨hz, hf1, hg1, hr1⟩ =>
    wp_li (by omega_using [hN']) fun s2 u2 => WP.block_nil ?_
  have iN : EngInv b p o N s N s2 := by
    refine ⟨Nat.le_refl _, hN, (u0.rest (by decide)).trans ((hr1.mono (by decide)).trans (u2.rest (by decide))),
      ?_, u2.gpr, ?_⟩
    · rw [u2.mem, ← u0.mem]; exact hf1.mono fun r hr => by simp [List.mem_singleton.mp hr]
    · have : (bytesAt s.mem p N).drop N = [] := by simp [bytesAt]
      rw [this, u2.mem, V, val32_congr (f := limb s1.mem b o) (g := fun _ => 0) (fun k hk => by
        rw [limb, hz k hk, u0.gpr]; rfl), val32_zero_fn]
      rw [show decodeLE [] = 0 from rfl, Nat.zero_mod]
  refine WP.loop (M := isa) (EngInv b p o N s) ?_ N s2 iN
  intro n t h
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by have := h.pos; omega_using [this]⟩
  have hk : k < N := by have := h.le; omega_using [this]
  have hct : Ctx b t := hc.of_rest h.rest (by decide)
  refine WP.mono (scalarByte_ok ho hct (p := p) (by rw [h.rest.gpr _ (by decide), h14]) (by omega_using [hN', hk]) h.r15
    (by rw [h.rest.rd, h.rest.wr]; exact hin k hk)
    (by rw [h.val]; exact Nat.mod_lt _ Proof.Ed448.order_pos)) fun t' ⟨rt, ft, r15, vt⟩ => ?_
  have hb : t.mem (p + BitVec.ofNat 64 k) = s.mem (p + BitVec.ofNat 64 k) :=
    h.frame _ fun r hr => hd k hk r hr
  have hv : V t'.mem b o = decodeLE ((bytesAt s.mem p N).drop k) % L := by
    rw [vt, h.val, hb, bytesAt_drop _ _ hk, Proof.Ed448.reduce_cons]
  have hz : (t'.gpr .r15 != 0) = decide (k ≠ 0) := by rw [r15, ofNat_ne_zero (by omega_using [hN', hk])]
  rw [eval_nonzero, hz]
  by_cases hk0 : k = 0
  · subst hk0
    refine .inl ⟨by simp, h.rest.trans rt, h.frame.trans ft, ?_⟩
    rw [hv, List.drop_zero]
  · exact .inr ⟨by simp [hk0], k, by omega_using [], ⟨by omega_using [hk], by omega_using [hk0], h.rest.trans rt, h.frame.trans ft, r15, hv⟩⟩

end

end VG.Proof.Ed448.PPC64LE

end

end

/-!
# `vg_ed448_scalar_reduce` on PPC64LE: correctness

The function saves the nonvolatile registers it uses at `SAVE` of `scratch`
(`saveList`, by `Spill`), reduces the 114 bytes of `wide` into `SR`
(`engine_ok`), writes `SR` to `out` as 57 bytes (`packScalar_ok`), and
restores the registers.
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE VG.Proof.X448.PPC64LE
open VG.Proof.X25519.PPC64LE hiding V FS V_lt pass_ok limb_frame
open VG.Spec.Ed448 (L decodeLE bytesAt)

/-! ## The saved registers -/

/-- The registers the scalar functions save, and their slots. -/
def saveList : List (Reg × Nat) := (List.range 12).map fun i => (savedRegs.getD i .r14, SAVE + 8 * i)

theorem scalarSave_eq (b : Reg) : scalarSave b = Spill.saveCode b saveList := by
  simp only [scalarSave, Spill.saveCode, saveList, List.map_map]; rfl

theorem scalarRestore_eq : scalarRestore = Spill.restoreCode .r6 saveList := by
  simp only [scalarRestore, Spill.restoreCode, saveList, List.map_map]; rfl

theorem saveList_fits : ∀ p ∈ saveList, p.2 % 8 = 0 ∧ p.2 < 32768 := by decide

theorem saveList_in : ∀ p ∈ saveList, SAVE ≤ p.2 ∧ p.2 + 8 ≤ SAVE + 96 := by decide

theorem saveList_restorable : Spill.Restorable .r6 saveList := by decide

theorem saveList_regs : saveList.map Prod.fst = savedRegs := by decide

theorem SAVE_eq : SAVE = 1064 := rfl
theorem SR_eq : SR = 0 := rfl

theorem rem_SR : Rem SR := ⟨by decide, by decide⟩

/-- A byte of a region disjoint from the working space is in none of its parts. -/
theorem not_in_ws {x b : Addr} {d n : Nat} (hd : d + n ≤ 8192)
    (h : ¬ (⟨b, 8192⟩ : Region).Contains x 1) : ¬ (⟨b + BitVec.ofNat 64 d, n⟩ : Region).Contains x 1 :=
  fun hc => h (Offset.sub_base b hd x hc)

/-- The bytes of a buffer apart from the working space, through a frame in it. -/
theorem bytesAt_keep {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {p b : Addr} {n : Nat}
    (hd : (⟨p, n⟩ : Region).Disjoint ⟨b, 8192⟩) (hs : ∀ r ∈ rs, Region.Sub r ⟨b, 8192⟩)
    (hn : n < 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt, List.map_inj_left]
  intro i hi
  have hi := List.mem_range.mp hi
  exact hf _ fun r hr hc => hd _ (Offset.contains_base _ (by omega_arith) (by omega_arith)) (hs r hr _ hc)

/-! ## The function -/

/-- The precondition, by register: `out` in `r3`, `wide` in `r4`, `scratch` in `r5`. -/
structure ReducePre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r4, 114⟩]
  wr : s.wr = [⟨s.gpr .r3, 57⟩, ⟨s.gpr .r5, 8192⟩]
  out_wide : (⟨s.gpr .r3, 57⟩ : Region).Disjoint ⟨s.gpr .r4, 114⟩
  out_ws : (⟨s.gpr .r3, 57⟩ : Region).Disjoint ⟨s.gpr .r5, 8192⟩
  wide_ws : (⟨s.gpr .r4, 114⟩ : Region).Disjoint ⟨s.gpr .r5, 8192⟩

section
variable {b : Addr}

/-- The remainder at `SR` to `out` (in `r27`), and the registers restored. -/
theorem finish_ok {s0 s : State} (hc : Ctx b s) {q : Addr} (h27 : s.gpr .r27 = q)
    (hw : (⟨q, 57⟩ : Region) ∈ s.wr) (hrd : s.rd = s0.rd) (hwr : s.wr = s0.wr)
    (hws : (⟨b, 8192⟩ : Region) ∈ s0.wr)
    (hd : (⟨q, 57⟩ : Region).Disjoint ⟨b, 8192⟩)
    (hsv : Spill.Saved b s0.gpr saveList s.mem)
    (hrest : ∀ r ∈ preserved, r ∉ savedRegs → s.gpr r = s0.gpr r) :
    WP isa (.block scalarFinish) s fun t =>
      (∀ r ∈ preserved, t.gpr r = s0.gpr r) ∧ t.sp = s.sp ∧
      bytesAt t.mem q 57 = Spec.Ed448.encodeLE 57 (V s.mem b SR) := by
  have hS := SR_eq
  have hV := SAVE_eq
  unfold scalarFinish
  rw [scalarRestore_eq]
  simp only [List.cons_append, List.nil_append]
  refine wp_addi (by decide) (by decide) fun s6 u6 => ?_
  have e14' : s6.gpr .r14 = q := by rw [u6.gpr, h27, BitVec.add_zero]
  have hc6 : Ctx b s6 := hc.of_rest (u6.rest (ws := [.r14]) (by decide)) (by decide)
  refine WP.append (packScalar_ok hc6 e14' (a := SR) (by omega_arith) (by rw [u6.wr]; exact hw)
    (hd.sub_right (Offset.sub_base _ (by omega_arith)))) fun s7 ⟨hr7, hf7, hb7⟩ => ?_
  have hsv7 : Spill.Saved b s0.gpr saveList s7.mem := by
    rw [← u6.mem] at hsv
    refine hsv.frame_in (lo := SAVE) (n := 96) saveList_in hf7 fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    exact fun x h₁ h₂ => hd x h₂ (Offset.sub_base _ (by omega_arith) x h₁)
  refine Spill.restore_ok (b := .r6) (B := b) (by decide)
    (by rw [hr7.gpr _ (by decide), u6.other _ (by decide), hc.r6])
    saveList_fits saveList_restorable
    (fun p hpl => by
      rw [hr7.rd, hr7.wr, u6.rd, u6.wr, hrd, hwr]
      exact in_base (List.mem_append_right _ hws) (by have := saveList_in p hpl; omega_arith)
        (by have := saveList_in p hpl; omega_arith)) hsv7 fun s8 h8 => WP.block_nil ⟨fun r hr => ?_, ?_, ?_⟩
  · refine h8.gpr_of ?_
    by_cases hm : r ∈ saveList.map Prod.fst
    · exact .inl hm
    · refine .inr ?_
      rw [saveList_regs] at hm
      have h1 : r ∉ ([.r7] : List Reg) := by revert hr hm; cases r <;> decide
      have h2 : r ∉ ([.r14] : List Reg) := by revert hr hm; cases r <;> decide
      rw [hr7.gpr _ h1, u6.other _ (by simpa using h2)]
      exact hrest r hr hm
  · rw [h8.sp, hr7.sp, u6.sp]
  · rw [h8.mem, hb7, u6.mem]

end

theorem reduce_ok {s : State} (hp : ReducePre s) :
    WP isa scalarReduce s fun t =>
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧
      bytesAt t.mem (s.gpr .r3) 57 = Spec.Ed448.scalarReduce (bytesAt s.mem (s.gpr .r4) 114) := by
  have hS := SR_eq
  have hD := SD_eq
  have hV := SAVE_eq
  have hws : (⟨s.gpr .r5, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hout : (⟨s.gpr .r3, 57⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hwide : (⟨s.gpr .r4, 114⟩ : Region) ∈ s.rd := by rw [hp.rd]; simp
  unfold scalarReduce scalarReduceSetup
  rw [scalarSave_eq]
  refine WP.seq (Spill.save_ok (b := .r5) (by decide) saveList_fits
    (fun p hpl => in_base hws (by have := saveList_in p hpl; omega_arith) (by have := saveList_in p hpl; omega_arith)) ?_)
  -- The state after the saves.
  let s1 : State := { s with mem := Spill.saveMem s.mem (s.gpr .r5) s.gpr saveList }
  have hsv : Spill.Saved (s.gpr .r5) s.gpr saveList s1.mem := Spill.saveMem_saved (by decide) _ _ _
  have hf1 : Frame [⟨s.gpr .r5, 8192⟩] s.mem s1.mem :=
    Spill.saveMem_frame_base (fun p hpl => by have := saveList_in p hpl; omega_arith) (by decide) _ _ _
  refine wp_addi (by decide) (by decide) fun s2 u2 => wp_addi (by decide) (by decide) fun s3 u3 =>
    wp_addi (by decide) (by decide) fun s4 u4 => WP.block_nil ?_
  have hr4 : Rest [.r6, .r14, .r27] s1 s4 :=
    (u2.rest (by decide)).trans ((u3.rest (by decide)).trans (u4.rest (by decide)))
  have hm4 : s4.mem = s1.mem := by rw [u4.mem, u3.mem, u2.mem]
  have e6 : s4.gpr .r6 = s.gpr .r5 := by
    rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr, BitVec.add_zero]
  have e27 : s4.gpr .r27 = s.gpr .r3 := by
    rw [u4.other _ (by decide), u3.gpr, u2.other _ (by decide), BitVec.add_zero]
  have e14 : s4.gpr .r14 = s.gpr .r4 := by
    rw [u4.gpr, u3.other _ (by decide), u2.other _ (by decide), BitVec.add_zero]
  have hc4 : Ctx (s.gpr .r5) s4 := ⟨e6, 8192, by decide, by rw [hr4.wr]; exact hws⟩
  -- The bytes of `wide`, kept by the saves.
  have hwb : ∀ i < 114, ¬ (⟨s.gpr .r5, 8192⟩ : Region).Contains (s.gpr .r4 + BitVec.ofNat 64 i) 1 :=
    fun i hi => hp.wide_ws _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
  have hb1 : bytesAt s4.mem (s.gpr .r4) 114 = bytesAt s.mem (s.gpr .r4) 114 := by
    rw [hm4]
    exact bytesAt_keep hf1 hp.wide_ws (fun r hr => by rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (Nat.le_refl _))
      (by decide)
  refine WP.seq (WP.mono (engine_ok rem_SR (N := 114) (by decide) (by decide) hc4 e14
    (fun i hi => by rw [hr4.rd, hr4.wr]; exact in_base (List.mem_append_left _ hwide) (by omega_arith) (by omega_arith))
    (fun i hi r hr => by
      simp only [RD, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact not_in_ws (by omega_arith) (hwb i hi))) fun s5 ⟨hr5, hf5, hv5⟩ => ?_)
  rw [hb1] at hv5
  have hc5 : Ctx (s.gpr .r5) s5 := hc4.of_rest hr5 (by decide)
  have hsv5 : Spill.Saved (s.gpr .r5) s.gpr saveList s5.mem := by
    rw [← hm4] at hsv
    refine hsv.frame_in (lo := SAVE) (n := 96) saveList_in hf5 fun r hr => ?_
    simp only [RD, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  refine WP.mono (finish_ok (s0 := s) hc5 (q := s.gpr .r3) (by rw [hr5.gpr _ (by decide), e27])
    (by rw [hr5.wr, hr4.wr]; exact hout) (by rw [hr5.rd, hr4.rd]) (by rw [hr5.wr, hr4.wr]) hws hp.out_ws hsv5
    fun r hr hm => ?_) fun t ⟨h1, h2, h3⟩ => ⟨h1, by rw [h2, hr5.sp, hr4.sp], by rw [h3, hv5]; rfl⟩
  have h3 : r ∉ ([.r5, .r7, .r8, .r11, .r15, .r16] : List Reg) := by revert hr hm; cases r <;> decide
  have h4 : r ∉ ([.r6, .r14, .r27] : List Reg) := by revert hr hm; cases r <;> decide
  rw [hr5.gpr _ h3, hr4.gpr _ h4]

end VG.Proof.Ed448.PPC64LE

end

end

/-! ### `Ed448.PPC64LE.ScalarVerified`, which only this module used -/

section

/-! ### `Ed448.PPC64LE.ScalarMulAdd`, which only this module used -/

section

/-!
# `vg_ed448_scalar_mul_add` on PPC64LE: correctness

The function saves the nonvolatile registers it uses, reduces `k`, `s` and
`r` modulo `L` into `SK`, `SS` and `SA` (`inputs_ok`, by `engine_ok`),
computes their product row by row at `ACC` (X448's rows, `product_ok`), adds
`SA` (`sum_ok`), stores the sum's 112 bytes at `WIDE`, reduces them modulo
`L` into `SR` (`engine_ok`) and writes `SR` to `out` (`finish_ok`). Below
`SAVE`, it writes only the working space's first 1064 bytes (`LOW`).
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE VG.Proof.X448.PPC64LE
open VG.Impl.X448.PPC64LE (pass ldSrc addSrc zeroAcc row ACC)
open VG.Proof.X25519.PPC64LE hiding V FS V_lt pass_ok limb_frame ACC_eq RowInv mulPre_ok row_ok
  zeroAcc_ok
open VG.Spec.Ed448 (L decodeLE bytesAt)

theorem SK_eq : SK = 112 := rfl
theorem SS_eq : SS = 168 := rfl
theorem SA_eq : SA = 224 := rfl
theorem WIDE_eq : WIDE = 280 := rfl

theorem rem_SK : Rem SK := ⟨by decide, by decide⟩
theorem rem_SS : Rem SS := ⟨by decide, by decide⟩
theorem rem_SA : Rem SA := ⟨by decide, by decide⟩

/-- What the function writes below `SAVE`. -/
abbrev LOW (b : Addr) : Region := ⟨b, 1064⟩

theorem sub_low (b : Addr) {d n : Nat} (h : d + n ≤ 1064) : Region.Sub ⟨b + BitVec.ofNat 64 d, n⟩ (LOW b) :=
  Offset.sub_base b h

theorem frame_low {b : Addr} {m m' : Mem} {rs : List Region} (hf : Frame rs m m')
    (hs : ∀ r ∈ rs, Region.Sub r (LOW b)) : Frame [LOW b] m m' :=
  hf.sub fun r hr => ⟨_, List.mem_singleton_self _, hs r hr⟩

theorem RD_low {b : Addr} {o : Nat} (ho : o + 56 ≤ 1064) : ∀ r ∈ RD b o, Region.Sub r (LOW b) := by
  intro r hr
  have hD := SD_eq
  simp only [RD, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact sub_low b (by omega_arith)

theorem low_ws (b : Addr) : Region.Sub (LOW b) ⟨b, 8192⟩ := Region.sub_prefix (by decide)

/-- The bytes of a buffer apart from the working space are in none of its parts. -/
theorem out_RD {q b : Addr} {N : Nat} (hN : N < 2 ^ 64) (hd : (⟨q, N⟩ : Region).Disjoint ⟨b, 8192⟩) {o : Nat} (ho : o + 56 ≤ 1064) :
    ∀ i < N, ∀ r ∈ RD b o, ¬ r.Contains (q + BitVec.ofNat 64 i) 1 := fun i hi r hr hc =>
  hd _ (Offset.contains_base _ (by omega_arith) (by omega_arith)) (low_ws b _ (RD_low ho r hr _ hc))

section
variable {b : Addr}

/-- `k`, `s` and `r` (at `r14`, `r17` and `r26`) modulo `L` into `SK`, `SS` and `SA`. -/
theorem inputs_ok {s : State} (hc : Ctx b s) {pk ps pr : Addr} (h14 : s.gpr .r14 = pk)
    (h17 : s.gpr .r17 = ps) (h26 : s.gpr .r26 = pr)
    (hk : (⟨pk, 57⟩ : Region) ∈ s.rd) (hs : (⟨ps, 57⟩ : Region) ∈ s.rd) (hr : (⟨pr, 57⟩ : Region) ∈ s.rd)
    (dk : (⟨pk, 57⟩ : Region).Disjoint ⟨b, 8192⟩) (ds : (⟨ps, 57⟩ : Region).Disjoint ⟨b, 8192⟩)
    (dr : (⟨pr, 57⟩ : Region).Disjoint ⟨b, 8192⟩) :
    WP isa scalarInputs s fun t =>
      Rest [.r5, .r7, .r8, .r11, .r14, .r15, .r16] s t ∧ Frame [LOW b] s.mem t.mem ∧
      V t.mem b SK = decodeLE (bytesAt s.mem pk 57) % L ∧ V t.mem b SS = decodeLE (bytesAt s.mem ps 57) % L ∧
      V t.mem b SA = decodeLE (bytesAt s.mem pr 57) % L := by
  have hK := SK_eq
  have hS := SS_eq
  have hA := SA_eq
  have hD := SD_eq
  obtain inr : ∀ (t : State) (q : Addr), t.rd = s.rd → t.wr = s.wr → (⟨q, 57⟩ : Region) ∈ s.rd →
      ∀ i < 57, InRegions (t.rd ++ t.wr) (q + BitVec.ofNat 64 i) 1 := fun t q h1 h2 hq i hi => by
    rw [h1, h2]; exact in_base (List.mem_append_left _ hq) (by omega_arith) (by omega_arith)
  obtain keep : ∀ {m m' : Mem} {o : Nat}, o + 56 ≤ 1064 → Frame (RD b o) m m' → ∀ (q : Addr),
      (⟨q, 57⟩ : Region).Disjoint ⟨b, 8192⟩ → bytesAt m' q 57 = bytesAt m q 57 := fun ho hf q hq =>
    bytesAt_keep hf hq (fun r hr x hx => low_ws b x (RD_low ho r hr x hx)) (by decide)
  obtain vkeep : ∀ {m m' : Mem} {o a : Nat}, Rem o → (o + 56 ≤ a ∨ a + 56 ≤ o) → Rem a → Frame (RD b a) m m' →
      V m' b o = V m b o := fun ho hoa ha hf => by
    have := ha.fits; have := ha.sep; have := ho.fits; have := ho.sep
    unfold V
    exact val32_congr (limb_frame hf fun r hr k hk => by
      simp only [RD, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith))
  unfold scalarInputs
  refine WP.seq (WP.mono (engine_ok rem_SK (N := 57) (by decide) (by decide) hc h14
    (inr s pk rfl rfl hk) (out_RD (by decide) dk (by omega_arith))) fun s1 ⟨r1, f1, v1⟩ => ?_)
  obtain hc1 : Ctx b s1 := hc.of_rest r1 (by decide)
  refine WP.seq (wp_addi (by decide) (by decide) fun s2 u2 => WP.block_nil ?_)
  obtain hc2 : Ctx b s2 := hc1.of_rest (u2.rest (ws := [.r14]) (by decide)) (by decide)
  obtain e14 : s2.gpr .r14 = ps := by rw [u2.gpr, r1.gpr _ (by decide), h17, BitVec.add_zero]
  refine WP.seq (WP.mono (engine_ok rem_SS (N := 57) (by decide) (by decide) hc2 e14
    (inr s2 ps (by rw [u2.rd, r1.rd]) (by rw [u2.wr, r1.wr]) hs) (out_RD (by decide) ds (by omega_arith)))
    fun s3 ⟨r3, f3, v3⟩ => ?_)
  obtain hc3 : Ctx b s3 := hc2.of_rest r3 (by decide)
  refine WP.seq (wp_addi (by decide) (by decide) fun s4 u4 => WP.block_nil ?_)
  obtain hc4 : Ctx b s4 := hc3.of_rest (u4.rest (ws := [.r14]) (by decide)) (by decide)
  obtain e14' : s4.gpr .r14 = pr := by
    rw [u4.gpr, r3.gpr _ (by decide), u2.other _ (by decide), r1.gpr _ (by decide), h26, BitVec.add_zero]
  refine WP.mono (engine_ok rem_SA (N := 57) (by decide) (by decide) hc4 e14'
    (inr s4 pr (by rw [u4.rd, r3.rd, u2.rd, r1.rd]) (by rw [u4.wr, r3.wr, u2.wr, r1.wr]) hr) (out_RD (by decide) dr (by omega_arith)))
    fun t ⟨rt, ft, vt⟩ => ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (r1.mono (by decide)).trans ((u2.rest (by decide)).trans ((r3.mono (by decide)).trans
      ((u4.rest (by decide)).trans (rt.mono (by decide)))))
  · rw [u4.mem] at ft
    rw [u2.mem] at f3
    exact (frame_low f1 (RD_low (by omega_arith))).trans ((frame_low f3 (RD_low (by omega_arith))).trans
      (frame_low ft (RD_low (by omega_arith))))
  · rw [vkeep rem_SK (by omega_arith) rem_SA ft, u4.mem, vkeep rem_SK (by omega_arith) rem_SS f3, u2.mem, v1]
  · rw [vkeep rem_SS (by omega_arith) rem_SA ft, u4.mem, v3, u2.mem, keep (by omega_arith) f1 ps ds]
  · rw [vt, u4.mem, keep (by omega_arith) f3 pr dr, u2.mem, keep (by omega_arith) f1 pr dr]

/-- The 28 limbs of the product of `SK` and `SS` at `ACC`. -/
theorem product_ok {s : State} (hc : Ctx b s) :
    WP isa scalarProduct s (RowInv b SK SS s 14) := by
  have hA := ACC_eq
  unfold scalarProduct
  refine WP.seq (WP.mono (mulPre_ok (x := SK) (y := SS) hc) fun s1 h1 => ?_)
  refine WP.loop (M := isa) (fun n s' => ∃ i, n = 14 - i ∧ i < 14 ∧ RowInv b SK SS s i s') ?_ 14 s1
    ⟨0, rfl, by decide, h1⟩
  rintro n s' ⟨i, rfl, hi, hr⟩
  refine WP.mono (row_ok (by decide) (by decide) hi hr) fun s'' ⟨hr', hz⟩ => ?_
  by_cases h14 : i + 1 = 14
  · refine .inl ⟨by rw [eval_nonzero, hz]; simp [h14], ?_⟩
    rw [h14] at hr'; exact hr'
  · exact .inr ⟨by rw [eval_nonzero, hz]; simp; omega_arith, 14 - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, hr'⟩

/-- The sum's limbs: the product plus `SA`, at `ACC`. -/
theorem wideAdd_ok {s : State} (hc : Ctx b s)
    (hb : val32 (accw ACC s.mem b) 28 + V s.mem b SA < 2 ^ 224 * 2 ^ 224 * (2 ^ 224 * 2 ^ 224)) :
    WP isa (.block (([.li .r8 0] : List Instr) ++ pass .r6 ACC (addSrc ACC SA) ++ pass .r6 (ACC + 56) (ldSrc (ACC + 56)))) s
      fun t => Rest [.r5, .r7, .r8] s t ∧ Frame [⟨b + BitVec.ofNat 64 ACC, 112⟩] s.mem t.mem ∧
        val32 (accw ACC t.mem b) 28 = val32 (accw ACC s.mem b) 28 + V s.mem b SA := by
  have hA := ACC_eq
  have hSA := SA_eq
  obtain hl : ∀ k < 28, accw ACC s.mem b k < 2 ^ 32 := fun k _ => wd_lt _ _ _
  obtain hr : ∀ k < 14, limb s.mem b SA k < 2 ^ 32 := fun k _ => limb_lt _ _ _ _
  simp only [List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s1 u1 => ?_
  obtain hc1 : Ctx b s1 := hc.of_rest (u1.rest (ws := [.r8]) (by decide)) (by decide)
  let c1 : Nat → Nat := fun k => accw ACC s.mem b k + limb s.mem b SA k
  refine WP.append (pass_ok (s0 := s1) (c := c1) (cin := 0) (by decide) (by decide) (by omega_arith)
    (fun k hk => by rw [hc1.r6]; exact hc1.inW (by omega_arith)) (by rw [u1.gpr]; rfl)
    (fun k hk => by have := hl k (by omega_arith); have := hr k hk; simp only [c1]; omega_arith) (by decide) ?_)
    fun s2 hp => ?_
  · intro k hk s' hp
    obtain hc' : Ctx b s' := hc1.of_rest hp.rest (by decide)
    simp only [Impl.X448.PPC64LE.addSrc]
    refine lw0_ok hc' (d := ACC + 4 * k) (by omega_arith) fun t1 v1 => ?_
    refine lw0_ok (hc'.of_rest (v1.rest (ws := [.r7]) (by decide)) (by decide)) (d := SA + 4 * k) (by omega_arith)
      fun t2 v2 => wp_add fun t3 v3 => WP.block_nil ⟨?_, ?_, by rw [v3.mem, v2.mem, v1.mem]⟩
    · have ea : wd s'.mem b (ACC + 4 * k) = accw ACC s.mem b k := by
        rw [wd_pass hc1 hp.frame (by omega_arith) (by omega_arith) (by omega_arith), u1.mem]; rfl
      obtain er : wd t1.mem b (SA + 4 * k) = limb s.mem b SA k := by
        rw [v1.mem, wd_pass hc1 hp.frame (by omega_arith) (by omega_arith) (by omega_arith), u1.mem]; rfl
      have := hl k (by omega_arith); have := hr k hk
      rw [v3.gpr, v2.other .r7 (by decide), v1.gpr, v2.gpr]
      unfold wd at ea er
      rw [toNat_add_lt (by rw [toNat_ext32, toNat_ext32, ea, er]; omega_arith), toNat_ext32, toNat_ext32, ea, er]
    · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans (v3.rest (by decide)))
  -- The high half, with the carry.
  obtain hr2 : Rest [.r5, .r7, .r8] s s2 := (u1.rest (by decide)).trans hp.rest
  obtain hc2 : Ctx b s2 := hc.of_rest hr2 (by decide)
  obtain hf2 : Frame [⟨b + BitVec.ofNat 64 ACC, 56⟩] s.mem s2.mem := by
    have := hp.frame; rw [hc1.r6] at this; rw [← u1.mem]; exact this
  obtain hlo : ∀ j < 14, accw ACC s2.mem b j = out c1 0 j := fun j hj => by
    have := hp.outs j hj; rwa [hc1.r6] at this
  obtain hhi : ∀ j < 14, accw ACC s2.mem b (14 + j) = accw ACC s.mem b (14 + j) := fun j hj => by
    unfold accw
    refine wd_frame hf2 fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  let c2 : Nat → Nat := fun k => accw ACC s.mem b (14 + k)
  obtain hc1v : val32 c1 14 = val32 (accw ACC s.mem b) 14 + V s.mem b SA := by
    simp only [c1]; rw [val32_add]; rfl
  obtain v1 := chain_val c1 0 14
  rw [pow448] at v1
  obtain hch1 : chain c1 0 14 ≤ 1 := by
    obtain h1 := val32_lt (f := accw ACC s.mem b) (n := 14) fun k hk => hl k (by omega_arith)
    obtain h2 := V_lt s.mem b SA
    rw [pow448] at h1
    omega_arith
  refine WP.mono (pass_ok (s0 := s2) (c := c2) (cin := chain c1 0 14) (by decide) (by decide) (by omega_arith)
    (fun k hk => by rw [hc2.r6]; exact hc2.inW (by omega_arith)) hp.r8
    (fun k hk => by have := hl (14 + k) (by omega_arith); simp only [c2]; omega_arith) (by omega_arith) ?_) fun t hq => ?_
  · intro k hk s' hq
    obtain hc' : Ctx b s' := hc2.of_rest hq.rest (by decide)
    refine WP.mono (ldSrc_ok hc' (o := ACC + 56) (k := k) (by omega_arith)) fun t1 ⟨e1, r1, m1⟩ =>
      ⟨?_, r1.mono (by decide), m1⟩
    rw [e1, wd_pass hc2 hq.frame (by omega_arith) (by omega_arith) (by omega_arith), show ACC + 56 + 4 * k = ACC + 4 * (14 + k) by omega_arith]
    exact hhi k hk
  · have hfq : Frame [⟨b + BitVec.ofNat 64 (ACC + 56), 56⟩] s2.mem t.mem := by
      have := hq.frame; rwa [hc2.r6] at this
    refine ⟨hr2.trans hq.rest, ?_, ?_⟩
    · refine (hf2.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
        (hfq.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
      · rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_arith)
      · rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_arith) (by omega_arith)
    · have hlo' : ∀ j < 14, accw ACC t.mem b j = out c1 0 j := fun j hj => by
        rw [← hlo j hj]
        unfold accw
        refine wd_frame hfq fun r hr => ?_
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
      obtain hhi' : ∀ j < 14, accw ACC t.mem b (14 + j) = out c2 (chain c1 0 14) j := fun j hj => by
        have := hq.outs j hj
        rw [hc2.r6] at this
        unfold accw
        rw [show ACC + 4 * (14 + j) = ACC + 56 + 4 * j by omega_arith]; exact this
      obtain v2 := chain_val c2 (chain c1 0 14) 14
      rw [pow448] at v2
      obtain hsum : val32 (accw ACC t.mem b) 28 =
          val32 (out c1 0) 14 + 2 ^ 224 * 2 ^ 224 * val32 (out c2 (chain c1 0 14)) 14 := by
        rw [show (28 : Nat) = 14 + 14 from rfl, val32_append, val32_congr hlo', val32_congr hhi', pow448]
      obtain hs28 : val32 (accw ACC s.mem b) 28 = val32 (accw ACC s.mem b) 14 + 2 ^ 224 * 2 ^ 224 * val32 c2 14 := by
        rw [show (28 : Nat) = 14 + 14 from rfl, val32_append, pow448]
      obtain ho2 := val32_lt (f := out c2 (chain c1 0 14)) (n := 14) fun k _ => out_lt _ _ _
      rw [pow448] at ho2
      -- The final carry is zero: the sum is below `2⁸⁹⁶`.
      obtain hch2 : chain c2 (chain c1 0 14) 14 = 0 := by
        rw [hs28] at hb
        have : val32 c2 14 + chain c1 0 14 < 2 ^ 224 * 2 ^ 224 := by
          rcases Nat.lt_or_ge (val32 c2 14 + chain c1 0 14) (2 ^ 224 * 2 ^ 224) with h' | h'
          · exact h'
          · exfalso
            have := Nat.mul_le_mul_left (2 ^ 224 * 2 ^ 224) h'
            omega_arith
        omega_arith
      rw [hch2, Nat.mul_zero, Nat.add_zero] at v2
      rw [hsum, v2]
      omega_arith

/-- `4n` bytes in memory, as the number of their words. -/
theorem decode_words (m : Mem) (q : Addr) (n : Nat) :
    decodeLE (bytesAt m q (4 * n)) = val32 (fun j => wd m q (4 * j)) n := by
  rw [Proof.Ed448.decodeLE_eq]
  exact leNum_bytesAt4 m q n

/-- `SA` added to the product, and the sum's 112 bytes to `WIDE`. -/
theorem sum_ok {s : State} (hc : Ctx b s)
    (hb : val32 (accw ACC s.mem b) 28 + V s.mem b SA < 2 ^ 224 * 2 ^ 224 * (2 ^ 224 * 2 ^ 224)) :
    WP isa (.block scalarSum) s fun t =>
      Rest [.r5, .r7, .r8, .r14] s t ∧ Frame [LOW b] s.mem t.mem ∧ t.gpr .r14 = b + BitVec.ofNat 64 WIDE ∧
      decodeLE (bytesAt t.mem (b + BitVec.ofNat 64 WIDE) 112) = val32 (accw ACC s.mem b) 28 + V s.mem b SA := by
  have hA := ACC_eq
  have hW := WIDE_eq
  unfold scalarSum
  rw [List.append_assoc (([.li .r8 0] : List Instr) ++ pass .r6 ACC (addSrc ACC SA) ++
    pass .r6 (ACC + 56) (ldSrc (ACC + 56))) ([.addi .r14 .r6 WIDE] : List Instr) (packWords ACC 28)]
  refine WP.append (wideAdd_ok hc hb) fun s1 ⟨r1, f1, v1⟩ => ?_
  obtain hc1 : Ctx b s1 := hc.of_rest r1 (by decide)
  rw [List.cons_append]
  refine wp_addi (by decide) (by decide) fun s2 u2 => ?_
  obtain e14 : s2.gpr .r14 = b + BitVec.ofNat 64 WIDE := by rw [u2.gpr, hc1.r6]
  obtain hc2 : Ctx b s2 := hc1.of_rest (u2.rest (ws := [.r14]) (by decide)) (by decide)
  refine WP.mono (packWords_ok hc2 e14 (a := ACC) (n := 28) (by omega_arith) (by decide)
    (fun k hk => by rw [Offset.add_add]; exact hc2.inW (by omega_arith))
    (Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith))) fun t ht => ⟨?_, ?_, ?_, ?_⟩
  · exact (r1.mono (by decide)).trans ((u2.rest (by decide)).trans (ht.rest.mono (by decide)))
  · have f2 := ht.frame
    rw [u2.mem] at f2
    exact (frame_low f1 fun r hr => by rw [List.mem_singleton.mp hr]; exact sub_low b (by omega_arith)).trans
      (frame_low f2 fun r hr => by rw [List.mem_singleton.mp hr]; exact sub_low b (by omega_arith))
  · rw [ht.rest.gpr _ (by decide), e14]
  · rw [show (112 : Nat) = 4 * 28 from rfl, decode_words, ← v1]
    exact val32_congr fun j hj => (ht.outs j hj).trans (by rw [limb, u2.mem]; rfl)

end

theorem mulAdd_mod (a b c n : Nat) : (a % n * (b % n) + c % n) % n = (c + a * b) % n := by
  rw [Nat.add_comm c, Nat.add_mod (a * b), Nat.mul_mod a b, Nat.mod_add_mod]

/-- The precondition, by register: `out` in `r3`, `r`, `k` and `s` in `r4`–`r6`, `scratch` in `r7`. -/
structure MulAddPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r4, 57⟩, ⟨s.gpr .r5, 57⟩, ⟨s.gpr .r6, 57⟩]
  wr : s.wr = [⟨s.gpr .r3, 57⟩, ⟨s.gpr .r7, 8192⟩]
  out_ws : (⟨s.gpr .r3, 57⟩ : Region).Disjoint ⟨s.gpr .r7, 8192⟩
  r_ws : (⟨s.gpr .r4, 57⟩ : Region).Disjoint ⟨s.gpr .r7, 8192⟩
  k_ws : (⟨s.gpr .r5, 57⟩ : Region).Disjoint ⟨s.gpr .r7, 8192⟩
  s_ws : (⟨s.gpr .r6, 57⟩ : Region).Disjoint ⟨s.gpr .r7, 8192⟩

theorem mulAdd_ok {s : State} (hp : MulAddPre s) :
    WP isa scalarMulAdd s fun t =>
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧
      bytesAt t.mem (s.gpr .r3) 57 = Spec.Ed448.scalarMulAdd (bytesAt s.mem (s.gpr .r4) 57)
        (bytesAt s.mem (s.gpr .r5) 57) (bytesAt s.mem (s.gpr .r6) 57) := by
  have hV := SAVE_eq
  have hA := ACC_eq
  have hS := SR_eq
  have hW := WIDE_eq
  have hD := SD_eq
  obtain ⟨b, hb⟩ : ∃ b, b = s.gpr .r7 := ⟨_, rfl⟩
  obtain hws : (⟨b, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr, hb]; simp
  obtain hout : (⟨s.gpr .r3, 57⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  unfold scalarMulAdd scalarMulAddArgs
  rw [scalarSave_eq]
  obtain hsin : ∀ p ∈ saveList, InRegions s.wr (s.gpr .r7 + BitVec.ofNat 64 p.2) 8 := fun p hpl => by
    have := saveList_in p hpl
    rw [← hb]; exact in_base hws (by omega_arith) (by omega_arith)
  refine WP.seq (Spill.save_ok (b := .r7) (by decide) saveList_fits hsin ?_)
  generalize hs1 : ({ s with mem := Spill.saveMem s.mem (s.gpr .r7) s.gpr saveList } : State) = s1
  obtain hsv : Spill.Saved b s.gpr saveList s1.mem := by rw [← hs1, hb]; exact Spill.saveMem_saved (by decide) _ _ _
  obtain hf1 : Frame [⟨b, 8192⟩] s.mem s1.mem := by
    rw [← hs1, hb]
    exact Spill.saveMem_frame_base (fun p hpl => by have := saveList_in p hpl; omega_arith) (by decide) _ _ _
  obtain hg1 : s1.gpr = s.gpr := by rw [← hs1]
  obtain hrd1 : s1.rd = s.rd := by rw [← hs1]
  obtain hwr1 : s1.wr = s.wr := by rw [← hs1]
  obtain hsp1 : s1.sp = s.sp := by rw [← hs1]
  refine wp_addi (by decide) (by decide) fun s2 u2 => wp_addi (by decide) (by decide) fun s3 u3 =>
    wp_addi (by decide) (by decide) fun s4 u4 => wp_addi (by decide) (by decide) fun s5 u5 =>
    wp_addi (by decide) (by decide) fun s6 u6 => WP.block_nil ?_
  obtain hr6 : Rest [.r6, .r14, .r17, .r26, .r27] s1 s6 :=
    (u2.rest (by decide)).trans ((u3.rest (by decide)).trans ((u4.rest (by decide)).trans
      ((u5.rest (by decide)).trans (u6.rest (by decide)))))
  obtain hm6 : s6.mem = s1.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem]
  obtain e6 : s6.gpr .r6 = b := by
    rw [u6.other _ (by decide), u5.gpr, u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
      BitVec.add_zero, hg1, hb]
  obtain e14 : s6.gpr .r14 = s.gpr .r5 := by
    rw [u6.gpr, u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
      BitVec.add_zero, hg1]
  obtain e17 : s6.gpr .r17 = s.gpr .r6 := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, u3.other _ (by decide), u2.other _ (by decide),
      BitVec.add_zero, hg1]
  obtain e26 : s6.gpr .r26 = s.gpr .r4 := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.gpr, u2.other _ (by decide),
      BitVec.add_zero, hg1]
  obtain e27 : s6.gpr .r27 = s.gpr .r3 := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.gpr,
      BitVec.add_zero, hg1]
  obtain hrd6 : s6.rd = s.rd := hr6.rd.trans hrd1
  obtain hwr6 : s6.wr = s.wr := hr6.wr.trans hwr1
  obtain hc6 : Ctx b s6 := ⟨e6, 8192, by decide, by rw [hwr6]; exact hws⟩
  obtain hin : ∀ r : Reg, r = .r4 ∨ r = .r5 ∨ r = .r6 → (⟨s.gpr r, 57⟩ : Region) ∈ s6.rd := by
    rintro r (rfl | rfl | rfl) <;> (rw [hrd6, hp.rd]; simp)
  -- The inputs' bytes, kept by the saves.
  obtain keep1 : ∀ q : Addr, (⟨q, 57⟩ : Region).Disjoint ⟨b, 8192⟩ → bytesAt s6.mem q 57 = bytesAt s.mem q 57 :=
    fun q hq => by
      rw [hm6]; exact bytesAt_keep hf1 hq (fun r hr => by rw [List.mem_singleton.mp hr]; exact fun _ h => h) (by decide)
  refine WP.seq (WP.mono (inputs_ok hc6 e14 e17 e26 (hin _ (.inr (.inl rfl))) (hin _ (.inr (.inr rfl)))
    (hin _ (.inl rfl)) (hb ▸ hp.k_ws) (hb ▸ hp.s_ws) (hb ▸ hp.r_ws)) fun s7 ⟨r7, f7, vk, vs, vr⟩ => ?_)
  rw [keep1 _ (hb ▸ hp.k_ws)] at vk
  rw [keep1 _ (hb ▸ hp.s_ws)] at vs
  rw [keep1 _ (hb ▸ hp.r_ws)] at vr
  obtain hc7 : Ctx b s7 := hc6.of_rest r7 (by decide)
  refine WP.seq (WP.mono (product_ok hc7) fun s8 h8 => ?_)
  have hc8 := h8.ctx
  obtain hvA : V s8.mem b SA = V s7.mem b SA := by
    unfold V
    exact val32_congr (limb_frame h8.frame fun r hr j hj => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by rw [SA_eq]; omega_arith)) (by rw [SA_eq]; omega_arith)
        (by omega_arith))
  obtain hKL : V s7.mem b SK < L := by rw [vk]; exact Nat.mod_lt _ Proof.Ed448.order_pos
  obtain hSL : V s7.mem b SS < L := by rw [vs]; exact Nat.mod_lt _ Proof.Ed448.order_pos
  obtain hAL : V s7.mem b SA < L := by rw [vr]; exact Nat.mod_lt _ Proof.Ed448.order_pos
  have hLt := L_lt
  obtain hprod : V s7.mem b SK * V s7.mem b SS ≤ (2 ^ 224 * 2 ^ 222) * (2 ^ 224 * 2 ^ 222) :=
    Nat.mul_le_mul (by omega_arith) (by omega_arith)
  have hv8 : val32 (accw ACC s8.mem b) 28 = V s7.mem b SK * V s7.mem b SS := h8.val
  refine WP.seq (WP.mono (sum_ok hc8 (by rw [hv8, hvA]; omega_arith)) fun s9 ⟨r9, f9, e9, v9⟩ => ?_)
  obtain hc9 : Ctx b s9 := hc8.of_rest r9 (by decide)
  refine WP.seq (WP.mono (engine_ok rem_SR (N := 112) (by decide) (by decide) hc9 e9
    (fun i hi => by rw [Offset.add_add]; exact hc9.inR (by omega_arith))
    (fun i hi r hr => by
      simp only [RD, List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [Offset.add_add]
      rcases hr with rfl | rfl <;>
        exact fun hc => Offset.disjoint b (d := WIDE + i) (n := 1) (k := 56) (.inr (by omega_arith))
          (by omega_arith) (by omega_arith) _ (Region.contains_self _ _) hc)) fun s10 ⟨r10, f10, v10⟩ => ?_)
  obtain hc10 : Ctx b s10 := hc9.of_rest r10 (by decide)
  -- The saved registers, through the writes below `SAVE`.
  obtain hlowsave : ∀ r ∈ [LOW b], Region.Disjoint ⟨b + BitVec.ofNat 64 SAVE, 96⟩ r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
  obtain hsv10 : Spill.Saved b s.gpr saveList s10.mem := by
    rw [← hm6] at hsv
    obtain f8 : Frame [LOW b] s7.mem s8.mem :=
      frame_low h8.frame fun r hr => by rw [List.mem_singleton.mp hr]; exact sub_low b (by omega_arith)
    exact ((((hsv.frame_in saveList_in f7 hlowsave).frame_in saveList_in f8 hlowsave).frame_in saveList_in f9
      hlowsave).frame_in saveList_in (frame_low f10 (RD_low (by omega_arith))) hlowsave)
  obtain hr610 : Rest [.r4, .r5, .r7, .r8, .r9, .r10, .r11, .r14, .r15, .r16] s6 s10 :=
    (r7.mono (by decide)).trans ((h8.rest.mono (by decide)).trans ((r9.mono (by decide)).trans (r10.mono (by decide))))
  refine WP.mono (finish_ok (s0 := s) hc10 (q := s.gpr .r3) (by rw [hr610.gpr _ (by decide), e27])
    (by rw [hr610.wr, hwr6]; exact hout) (by rw [hr610.rd, hrd6]) (by rw [hr610.wr, hwr6]) hws (hb ▸ hp.out_ws) hsv10
    fun r hr hm => ?_) fun t ⟨h1, h2, h3⟩ => ⟨h1, by rw [h2, hr610.sp, hr6.sp, hsp1], ?_⟩
  · have h3 : r ∉ ([.r4, .r5, .r7, .r8, .r9, .r10, .r11, .r14, .r15, .r16] : List Reg) := by
      revert hr hm; cases r <;> decide
    obtain h4 : r ∉ ([.r6, .r14, .r17, .r26, .r27] : List Reg) := by revert hr hm; cases r <;> decide
    rw [hr610.gpr _ h3, hr6.gpr _ h4, hg1]
  · rw [h3, v10, v9, hv8, hvA, vk, vs, vr]
    unfold Spec.Ed448.scalarMulAdd
    exact congrArg (Spec.Ed448.encodeLE 57) (mulAdd_mod _ _ _ _)

end VG.Proof.Ed448.PPC64LE

end

end


/-!
# `vg_ed25519_scalar_reduce` and `vg_ed25519_scalar_mul_add` on PPC64LE, verified

Each function meets its contract of `Spec/Ed448/Contract.lean`, with no
stack: the proof against the contract's facts by register (`reducePPC`,
`mulAddPPC`), which it implies, and a state satisfying it. The functions save
and restore the nonvolatile registers they write (`reduce_ok`, `mulAdd_ok`),
and never write the link register or call another.
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG VG.PPC64LE

/-- `scalarReduceContract` by register. -/
def reducePPC : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, 57⟩
    let wide : Region := ⟨s.gpr .r4, 114⟩
    let ws : Region := ⟨s.gpr .r5, 8192⟩
    s.rd = [wide] ∧ s.wr = [out, ws] ∧ out.Disjoint wide ∧ out.Disjoint ws ∧ wide.Disjoint ws
  post s s' := Spec.Ed448.bytesAt s'.mem (s.gpr .r3) 57 =
    Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt s.mem (s.gpr .r4) 114)
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.sp = s₂.sp

theorem reduce_ok' (s : State) (hs : reducePPC.pre s) :
    ∃ t s', VG.Exec isa Impl.Ed448.PPC64LE.scalarReduce s t s' ∧ abiPreserved s s' ∧
      reducePPC.post s s' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs
  obtain ⟨t, s', he, hg, hsp, hb⟩ := reduce_ok ⟨h1, h2, h3, h4, h5⟩
  exact ⟨t, s', he, ⟨hg, hsp, Exec.lr he (by decide +kernel) (by rw [← Code.allInstrs_eq]; decide +kernel)⟩, hb⟩

/-- `scalarMulAddContract` by register. -/
def mulAddPPC : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, 57⟩
    let r : Region := ⟨s.gpr .r4, 57⟩
    let k : Region := ⟨s.gpr .r5, 57⟩
    let a : Region := ⟨s.gpr .r6, 57⟩
    let ws : Region := ⟨s.gpr .r7, 8192⟩
    s.rd = [r, k, a] ∧ s.wr = [out, ws] ∧ out.Disjoint ws ∧ r.Disjoint ws ∧ k.Disjoint ws ∧ a.Disjoint ws
  post s s' := Spec.Ed448.bytesAt s'.mem (s.gpr .r3) 57 =
    Spec.Ed448.scalarMulAdd (Spec.Ed448.bytesAt s.mem (s.gpr .r4) 57)
      (Spec.Ed448.bytesAt s.mem (s.gpr .r5) 57) (Spec.Ed448.bytesAt s.mem (s.gpr .r6) 57)
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.sp = s₂.sp

theorem mulAdd_ok' (s : State) (hs : mulAddPPC.pre s) :
    ∃ t s', VG.Exec isa Impl.Ed448.PPC64LE.scalarMulAdd s t s' ∧ abiPreserved s s' ∧
      mulAddPPC.post s s' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hs
  obtain ⟨t, s', he, hg, hsp, hb⟩ := mulAdd_ok ⟨h1, h2, h3, h4, h5, h6⟩
  exact ⟨t, s', he, ⟨hg, hsp, Exec.lr he (by decide +kernel) (by rw [← Code.allInstrs_eq]; decide +kernel)⟩, hb⟩

end VG.Proof.Ed448.PPC64LE

end

end


/-!
# Ed448's whole functions on PPC64LE: the calls of the Ed448 functions

`base_call`, `reduce_call`, `mulAdd_call` and `veq_call`: a call of
`vg_ed448_scalar_base`, `vg_ed448_scalar_reduce`, `vg_ed448_scalar_mul_add`
or `vg_ed448_verify_equation` with its arguments in `r3`–`r7`, by its
contract by register (`basePPC`, …): what it writes, that it keeps the
callee-saved registers, and its result. None of them has a frame
(`*_noFrames`, checked once here).
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE.Whole

open VG VG.PPC64LE
open VG.Spec.Ed448 (bytesAt)

theorem base_noFrames : Impl.Ed448.PPC64LE.scalarBase.noFrames = true := by decide +kernel
theorem reduce_noFrames : Impl.Ed448.PPC64LE.scalarReduce.noFrames = true := by decide +kernel
theorem mulAdd_noFrames : Impl.Ed448.PPC64LE.scalarMulAdd.noFrames = true := by decide +kernel
theorem veq_noFrames : Impl.Ed448.PPC64LE.verifyEquation.noFrames = true := by decide +kernel

theorem ce_gpr (s : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs) :
    (s.callEntry.withRegions rd wr).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

section
variable {s : State} {Q : State → Prop}

theorem base_call (hl : Proof.Ed448.BaseLadder2Ok) {out sc ws : Addr} (h3 : s.gpr .r3 = out)
    (h4 : s.gpr .r4 = sc) (h5 : s.gpr .r5 = ws) (d₀ : Region.Disjoint ⟨out, 57⟩ ⟨sc, 57⟩)
    (d₁ : Region.Disjoint ⟨out, 57⟩ ⟨ws, 8192⟩)
    (d₂ : Region.Disjoint ⟨sc, 57⟩ ⟨ws, 8192⟩)
    (hc : Covers ([⟨sc, 57⟩] ++ [⟨out, 57⟩, ⟨ws, 8192⟩]) (s.rd ++ s.wr)) (hw : Covers [⟨out, 57⟩, ⟨ws, 8192⟩] s.wr)
    (k : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Frame [⟨out, 57⟩, ⟨ws, 8192⟩] s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      bytesAt s'.mem out 57 = Spec.Ed448.scalarBase (bytesAt s.mem sc 57) → Q s') :
    WP isa (.call "vg_ed448_scalar_base" Impl.Ed448.PPC64LE.scalarBase) s Q := by
  refine WP.call (k := basePPC) (scalarBase_ok hl) (rd := [⟨sc, 57⟩]) (wr := [⟨out, 57⟩, ⟨ws, 8192⟩])
    ⟨by rw [State.withRegions_rd, ce_gpr _ _ _ (by decide), h4],
      by rw [State.withRegions_wr, ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h3, h5],
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h3, h4]; exact d₀,
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h3, h5]; exact d₁,
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h4, h5]; exact d₂⟩ hc hw
    (fun s' a b c f g _ hp => k s' a b c f g ?_) base_noFrames
  simp only [basePPC, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
    State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r4 ∉ linkRegs by decide),
    h3, h4] at hp
  exact hp

theorem reduce_call {out wide ws : Addr} (h3 : s.gpr .r3 = out) (h4 : s.gpr .r4 = wide) (h5 : s.gpr .r5 = ws)
    (d₁ : Region.Disjoint ⟨out, 57⟩ ⟨wide, 114⟩) (d₂ : Region.Disjoint ⟨out, 57⟩ ⟨ws, 8192⟩)
    (d₃ : Region.Disjoint ⟨wide, 114⟩ ⟨ws, 8192⟩)
    (hc : Covers ([⟨wide, 114⟩] ++ [⟨out, 57⟩, ⟨ws, 8192⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨out, 57⟩, ⟨ws, 8192⟩] s.wr)
    (k : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Frame [⟨out, 57⟩, ⟨ws, 8192⟩] s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      bytesAt s'.mem out 57 = Spec.Ed448.scalarReduce (bytesAt s.mem wide 114) → Q s') :
    WP isa (.call "vg_ed448_scalar_reduce" Impl.Ed448.PPC64LE.scalarReduce) s Q := by
  refine WP.call (k := reducePPC) reduce_ok' (rd := [⟨wide, 114⟩]) (wr := [⟨out, 57⟩, ⟨ws, 8192⟩])
    ⟨by rw [State.withRegions_rd, ce_gpr _ _ _ (by decide), h4],
      by rw [State.withRegions_wr, ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h3, h5],
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h3, h4]; exact d₁,
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h3, h5]; exact d₂,
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h4, h5]; exact d₃⟩ hc hw
    (fun s' a b c f g _ hp => k s' a b c f g ?_) reduce_noFrames
  simp only [reducePPC, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
    State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r4 ∉ linkRegs by decide),
    h3, h4] at hp
  exact hp

theorem mulAdd_call {out r k a ws : Addr} (h3 : s.gpr .r3 = out) (h4 : s.gpr .r4 = r) (h5 : s.gpr .r5 = k)
    (h6 : s.gpr .r6 = a) (h7 : s.gpr .r7 = ws) (d₁ : Region.Disjoint ⟨out, 57⟩ ⟨ws, 8192⟩)
    (d₂ : Region.Disjoint ⟨r, 57⟩ ⟨ws, 8192⟩) (d₃ : Region.Disjoint ⟨k, 57⟩ ⟨ws, 8192⟩)
    (d₄ : Region.Disjoint ⟨a, 57⟩ ⟨ws, 8192⟩)
    (hc : Covers ([⟨r, 57⟩, ⟨k, 57⟩, ⟨a, 57⟩] ++ [⟨out, 57⟩, ⟨ws, 8192⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨out, 57⟩, ⟨ws, 8192⟩] s.wr)
    (K : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Frame [⟨out, 57⟩, ⟨ws, 8192⟩] s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      bytesAt s'.mem out 57 = Spec.Ed448.scalarMulAdd (bytesAt s.mem r 57) (bytesAt s.mem k 57)
        (bytesAt s.mem a 57) → Q s') :
    WP isa (.call "vg_ed448_scalar_mul_add" Impl.Ed448.PPC64LE.scalarMulAdd) s Q := by
  refine WP.call (k := mulAddPPC) mulAdd_ok' (rd := [⟨r, 57⟩, ⟨k, 57⟩, ⟨a, 57⟩]) (wr := [⟨out, 57⟩, ⟨ws, 8192⟩])
    ⟨by rw [State.withRegions_rd, ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide),
        h4, h5, h6],
      by rw [State.withRegions_wr, ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h3, h7],
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h3, h7]; exact d₁,
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h4, h7]; exact d₂,
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h5, h7]; exact d₃,
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h6, h7]; exact d₄⟩ hc hw
    (fun s' a b c f g _ hp => K s' a b c f g ?_) mulAdd_noFrames
  simp only [mulAddPPC, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
    State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r4 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.r5 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r6 ∉ linkRegs by decide),
    h3, h4, h5, h6] at hp
  exact hp

theorem veq_call (hR : Proof.Ed448.RecoverOk) {pk sig ch ws : Addr}
    (h3 : s.gpr .r3 = pk) (h4 : s.gpr .r4 = sig) (h5 : s.gpr .r5 = ch) (h6 : s.gpr .r6 = ws)
    (d₁ : Region.Disjoint ⟨pk, 57⟩ ⟨ws, 8192⟩) (d₂ : Region.Disjoint ⟨sig, 114⟩ ⟨ws, 8192⟩)
    (d₃ : Region.Disjoint ⟨ch, 57⟩ ⟨ws, 8192⟩)
    (hc : Covers ([⟨pk, 57⟩, ⟨sig, 114⟩, ⟨ch, 57⟩] ++ [⟨ws, 8192⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨ws, 8192⟩] s.wr)
    (k : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Frame [⟨ws, 8192⟩] s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      (s'.gpr .r3).setWidth 32 = (if Spec.Ed448.verifyEquation (bytesAt s.mem pk 57) (bytesAt s.mem sig 114)
        (bytesAt s.mem ch 57) then 1 else 0) → Q s') :
    WP isa (.call "vg_ed448_verify_equation" Impl.Ed448.PPC64LE.verifyEquation) s Q := by
  refine WP.call (k := verifyPPC) (verifyEquation_ok hR) (rd := [⟨pk, 57⟩, ⟨sig, 114⟩, ⟨ch, 57⟩])
    (wr := [⟨ws, 8192⟩])
    ⟨by rw [State.withRegions_rd, ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide),
        h3, h4, h5],
      by rw [State.withRegions_wr, ce_gpr _ _ _ (by decide), h6],
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h3, h6]; exact d₁,
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h4, h6]; exact d₂,
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h5, h6]; exact d₃⟩ hc hw
    (fun s' a b c f g _ hp => k s' a b c f g ?_) veq_noFrames
  simp only [verifyPPC, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
    State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r4 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.r5 ∉ linkRegs by decide), h3, h4, h5] at hp
  exact hp

end

end VG.Proof.Ed448.PPC64LE.Whole

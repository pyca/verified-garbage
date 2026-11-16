module

public import VerifiedGarbage.Proof.X25519.Contract
import VerifiedGarbage.Proof.X25519.PPC64LE.Bits
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.X25519.PPC64LE.Setup
public import VerifiedGarbage.Proof.X25519.PPC64LE.Fe51.Ladder
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.PPC64LE.RunR
import VerifiedGarbage.Proof.X25519.PPC64LE.Mul
import VerifiedGarbage.Proof.X25519.PPC64LE.Freeze
import VerifiedGarbage.Proof.X25519.PPC64LE.Cswap
import VerifiedGarbage.Proof.X25519.PPC64LE.Reduce
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Spec.X25519.Contract
import VerifiedGarbage.Proof.X25519.PPC64LE.CT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.PPC64LE.Untouched
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint

/-!
# X25519 on PPC64LE: the whole function

`vg_x25519` writes `X25519(k, u)` to `out` (`x25519_correct`). The
u-coordinate is decoded to four words, as the other curves' code on this
target reads it, and the scalar to its bits; the ladder and the inversion
work on five 51-bit limbs (`unpack_ok`, `Fe51/Ladder.lean`), whose result
`pack` gives back as four words (`pack_ok`) for the last reduction.
-/

@[expose] public section

namespace VG.Proof.X25519.PPC64LE.Fe51

open VG VG.PPC64LE VG.Impl.X25519.PPC64LE.Fe51
open VG.Spec.X25519 (P Fe)
open VG.Proof.X25519 (toFe)
open VG.Proof.X25519.PPC64LE (Ctx Rest Upd UpdC Mupd V dw ew val4 V_eq4 wp_li wp_lsl wp_subi ld0_ok wp_addc
  wp_addze stores4_ok rv4)

theorem tn_addm {x y : BitVec 64} {a c : Nat} (hx : x.toNat = a) (hy : y.toNat = c) :
    (x + y).toNat = (a + c) % 2 ^ 64 := by rw [BitVec.toNat_add, hx, hy]

theorem tn_shlm {x : BitVec 64} {a : Nat} (hx : x.toNat = a) (n : Nat) :
    (x <<< n).toNat = a * 2 ^ n % 2 ^ 64 := by rw [toNat_shl, hx]

/-! ## Four words to five limbs -/

/-- The limbs of the words in `r7`–`r10`, in `ra`. -/
def unpackB : List Instr :=
  [.logic .and .r14 .r7 .r4,
    .lsr .d .r15 .r7 51, .lsl .r5 .r8 13, .add .r15 .r15 .r5, .logic .and .r15 .r15 .r4,
    .lsr .d .r16 .r8 38, .lsl .r5 .r9 26, .add .r16 .r16 .r5, .logic .and .r16 .r16 .r4,
    .lsr .d .r17 .r9 25, .lsl .r5 .r10 39, .add .r17 .r17 .r5, .logic .and .r17 .r17 .r4,
    .lsr .d .r18 .r10 12]

/-- `unpack` before its stores. -/
def unpackR : List Instr :=
  mask51 ++ (List.range 4).map (fun k => .load .d (lo k) .r6 (U + 8 * k)) ++ unpackB

theorem unpack_eq : unpack = unpackR ++ (stores ra X1 ++ (stores ra X3 ++ (([.li .r7 1, .li .r8 0] : List Instr) ++
    (stores one X2 ++ (stores (fun _ => .r8) Z2 ++ stores one Z3))))) := by
  simp only [unpack, unpackR, unpackB, List.append_assoc]

theorem unpackB_ok {t : State} {w0 w1 w2 w3 : Nat} (h7 : (t.gpr .r7).toNat = w0)
    (h8 : (t.gpr .r8).toNat = w1) (h9 : (t.gpr .r9).toNat = w2) (h10 : (t.gpr .r10).toNat = w3)
    (hm : (t.gpr .r4).toNat = 2 ^ 51 - 1) (b0 : w0 < 2 ^ 64) (b1 : w1 < 2 ^ 64) (b2 : w2 < 2 ^ 64)
    (b3 : w3 < 2 ^ 63) :
    WP isa (.block unpackB) t fun s' => ∃ l0 l1 l2 l3 l4 : Nat, (s'.gpr .r14).toNat = l0 ∧
      (s'.gpr .r15).toNat = l1 ∧ (s'.gpr .r16).toNat = l2 ∧ (s'.gpr .r17).toNat = l3 ∧
      (s'.gpr .r18).toNat = l4 ∧ s'.mem = t.mem ∧
      (val5 (lim l0 l1 l2 l3 l4) = w0 + 2 ^ 64 * (w1 + 2 ^ 64 * (w2 + 2 ^ 64 * w3)) ∧
      l0 < 2 ^ 51 ∧ l1 < 2 ^ 51 ∧ l2 < 2 ^ 51 ∧ l3 < 2 ^ 51 ∧ l4 < 2 ^ 51) := by
  have e0 := tn_mask h7 hm
  have e1 := tn_mask (tn_addm (tn_shr h7 51) (tn_shlm h8 13)) hm
  have e2 := tn_mask (tn_addm (tn_shr h8 38) (tn_shlm h9 26)) hm
  have e3 := tn_mask (tn_addm (tn_shr h9 25) (tn_shlm h10 39)) hm
  have e4 := tn_shr h10 12
  crunr [unpackB]
  exact ⟨_, _, _, _, _, e0, e1, e2, e3, e4, unpack_val b0 b1 b2 b3 rfl rfl rfl rfl rfl⟩

/-- The registers `unpack` writes. -/
abbrev unpackRegs : List Reg := [.r4, .r5, .r7, .r8, .r9, .r10, .r11, .r14, .r15, .r16, .r17, .r18]

theorem unpackR_writes : writesOnly unpackRegs (.block unpackR) = true := by decide +kernel

section
variable {b : Addr}

theorem unpackR_ok {s : State} (hc : Ctx b s) {w : Nat} (hw : V s.mem b U = w) (hlt : w < 2 ^ 255) :
    WP isa (.block unpackR) s fun s' => ∃ l0 l1 l2 l3 l4 : Nat, (s'.gpr .r14).toNat = l0 ∧
      (s'.gpr .r15).toNat = l1 ∧ (s'.gpr .r16).toNat = l2 ∧ (s'.gpr .r17).toNat = l3 ∧
      (s'.gpr .r18).toNat = l4 ∧ s'.mem = s.mem ∧
      (val5 (lim l0 l1 l2 l3 l4) = w ∧
      l0 < 2 ^ 51 ∧ l1 < 2 ^ 51 ∧ l2 < 2 ^ 51 ∧ l3 < 2 ^ 51 ∧ l4 < 2 ^ 51) := by
  have hV : w = val4 (ew s.mem b U) := by rw [← hw, V_eq4]
  have d0 := dw_lt s.mem b (U + 8 * 0); have d1 := dw_lt s.mem b (U + 8 * 1)
  have d2 := dw_lt s.mem b (U + 8 * 2); have d3 := dw_lt s.mem b (U + 8 * 3)
  have d3' : dw s.mem b (U + 8 * 3) < 2 ^ 63 := by
    simp only [val4, ew] at hV; omega_using [hV, hlt, d0, d1, d2]
  simp only [unpackR, mask51, lo, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ]
  refine wp_li (by decide) fun s1 u1 => wp_lsl (by decide) fun s2 u2 =>
    wp_subi (by decide) (by decide) fun s3 u3 => ?_
  have hc3 : Ctx b s3 := ((hc.of_rest (u1.rest (ws := [.r4]) (by decide)) (by decide)).of_rest
    (u2.rest (ws := [.r4]) (by decide)) (by decide)).of_rest (u3.rest (ws := [.r4]) (by decide)) (by decide)
  have m3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  refine ld0_ok hc3 (by decide) (by decide) fun s4 u4 => ?_
  have hc4 := hc3.of_rest (u4.rest (ws := [.r7]) (by decide)) (by decide)
  refine ld0_ok hc4 (by decide) (by decide) fun s5 u5 => ?_
  have hc5 := hc4.of_rest (u5.rest (ws := [.r8]) (by decide)) (by decide)
  refine ld0_ok hc5 (by decide) (by decide) fun s6 u6 => ?_
  have hc6 := hc5.of_rest (u6.rest (ws := [.r9]) (by decide)) (by decide)
  refine ld0_ok hc6 (by decide) (by decide) fun s7 u7 => ?_
  have m7 : s7.mem = s.mem := by rw [u7.mem, u6.mem, u5.mem, u4.mem, m3]
  have h7 : (s7.gpr .r7).toNat = dw s.mem b (U + 8 * 0) := by
    rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.gpr, m3]; rfl
  have h8 : (s7.gpr .r8).toNat = dw s.mem b (U + 8 * 1) := by
    rw [u7.other _ (by decide), u6.other _ (by decide), u5.gpr, u4.mem, m3]; rfl
  have h9 : (s7.gpr .r9).toNat = dw s.mem b (U + 8 * 2) := by
    rw [u7.other _ (by decide), u6.gpr, u5.mem, u4.mem, m3]; rfl
  have h10 : (s7.gpr .r10).toNat = dw s.mem b (U + 8 * 3) := by
    rw [u7.gpr, u6.mem, u5.mem, u4.mem, m3]; rfl
  have hm : (s7.gpr .r4).toNat = 2 ^ 51 - 1 := by
    rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.gpr, u2.gpr, u1.gpr]; exact m51
  refine WP.mono (unpackB_ok h7 h8 h9 h10 hm d0 d1 d2 d3') fun s' ⟨l0, l1, l2, l3, l4, e0, e1, e2, e3, e4,
    hm', hv, hb⟩ => ⟨l0, l1, l2, l3, l4, e0, e1, e2, e3, e4, hm'.trans m7, by rw [hv, hV]; rfl, hb⟩

/-- `stores rs o` of limbs `f`: the element at the slot `o`. -/
theorem slot_store {rs : Nat → Reg} {o : Nat} (ho : isSlot o = true) {qs : List Nat} {v : Nat → Fe}
    {s : State} (hc : Ctx b s) (hS : SlotsOk s.mem b qs v) {f : Nat → Nat}
    (hf : ∀ k < 5, (s.gpr (rs k)).toNat = f k) (hb : ∀ k < 5, f k < 2 ^ 51 + 2 ^ 18) :
    WP isa (.block (stores rs o)) s fun s' => Rest [] s s' ∧ Frame [FB b] s.mem s'.mem ∧
      SlotsOk s'.mem b (o :: qs) (upd v o (toFe (val5 f))) := by
  have lo := isSlot_le ho
  refine WP.mono (stores_ok rs (by omega_using [lo]) lo.2.2 hc) fun s' ⟨hw, hfr, hr⟩ =>
    ⟨hr, frame_FB ho hfr, hS.write ho hfr (fun k hk => by rw [hw k hk, hf k hk]; exact hb k hk)
      (by rw [FS, V5, val5_congr fun k hk => by rw [hw k hk, hf k hk]])⟩

theorem lim_lt {l0 l1 l2 l3 l4 n : Nat} (h0 : l0 < n) (h1 : l1 < n) (h2 : l2 < n) (h3 : l3 < n)
    (h4 : l4 < n) : ∀ k < 5, lim l0 l1 l2 l3 l4 k < n := fun k hk => by
  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega_using [hk]
  rcases this with rfl | rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3, h4]

/-- `unpack`: the ladder's first state, from the u-coordinate's words. -/
theorem unpack_ok {s : State} (hc : Ctx b s) {w : Nat} (hw : V s.mem b U = w) (hlt : w < 2 ^ 255) :
    WP isa (.block unpack) s fun s' => Stp b s s' ∧ Ctx b s' ∧
      SlotsOk s'.mem b LQ (ladV (toFe w) (VG.Proof.X25519.init (toFe w))) := by
  rw [unpack_eq]
  refine WP.append (WP.rest unpackRegs (unpackR_ok hc hw hlt) unpackR_writes)
    fun s1 ⟨⟨l0, l1, l2, l3, l4, e0, e1, e2, e3, e4, m1, hval, b0, b1, b2, b3, b4⟩, hr1⟩ => ?_
  have hc1 := hc.of_rest hr1 (by decide)
  have hreg : ∀ k < 5, (s1.gpr (ra k)).toNat = lim l0 l1 l2 l3 l4 k := fun k hk => by
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega_using [hk]
    rcases this with rfl | rfl | rfl | rfl | rfl
    exacts [e0, e1, e2, e3, e4]
  have hbl : ∀ k < 5, lim l0 l1 l2 l3 l4 k < 2 ^ 51 + 2 ^ 18 := lim_lt (by omega_using [b0])
    (by omega_using [b1]) (by omega_using [b2]) (by omega_using [b3]) (by omega_using [b4])
  have hS1 : SlotsOk s1.mem b [] (fun _ => 0) := fun q hq => absurd hq List.not_mem_nil
  refine WP.append (slot_store (o := X1) (by decide) hc1 hS1 hreg hbl) fun s2 ⟨r2, f2, hS2⟩ => ?_
  have hc2 := hc1.of_rest r2 (by decide)
  refine WP.append (slot_store (o := X3) (f := lim l0 l1 l2 l3 l4) (by decide) hc2 hS2
    (fun k hk => by rw [r2.gpr _ (by simp)]; exact hreg k hk) hbl) fun s3 ⟨r3, f3, hS3⟩ => ?_
  have hc3 := hc2.of_rest r3 (by decide)
  simp only [List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s4 u4 => wp_li (by decide) fun s5 u5 => ?_
  have r5 : Rest [.r7, .r8] s3 s5 := (u4.rest (by decide)).trans (u5.rest (by decide))
  have hc5 := hc3.of_rest r5 (by decide)
  have m5 : s5.mem = s3.mem := by rw [u5.mem, u4.mem]
  have h7 : (s5.gpr .r7).toNat = 1 := by rw [u5.other _ (by decide), u4.gpr]; rfl
  have h8 : (s5.gpr .r8).toNat = 0 := by rw [u5.gpr]; rfl
  have hone : ∀ k < 5, (s5.gpr (one k)).toNat = lim 1 0 0 0 0 k := fun k hk => by
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega_using [hk]
    rcases this with rfl | rfl | rfl | rfl | rfl
    exacts [h7, h8, h8, h8, h8]
  have hzero : ∀ k < 5, (s5.gpr .r8).toNat = lim 0 0 0 0 0 k := fun k hk => by
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega_using [hk]
    rcases this with rfl | rfl | rfl | rfl | rfl <;> exact h8
  rw [← m5] at hS3
  refine WP.append (slot_store (o := X2) (by decide) hc5 hS3 hone
    (lim_lt (by decide) (by decide) (by decide) (by decide) (by decide))) fun s6 ⟨r6, f6, hS6⟩ => ?_
  have hc6 := hc5.of_rest r6 (by decide)
  refine WP.append (slot_store (rs := fun _ => .r8) (o := Z2) (f := lim 0 0 0 0 0) (by decide) hc6 hS6
    (fun k hk => by rw [r6.gpr _ (by simp)]; exact hzero k hk)
    (lim_lt (by decide) (by decide) (by decide) (by decide) (by decide))) fun s7 ⟨r7, f7, hS7⟩ => ?_
  have hc7 := hc6.of_rest r7 (by decide)
  refine WP.mono (slot_store (o := Z3) (f := lim 1 0 0 0 0) (by decide) hc7 hS7
    (fun k hk => by rw [r7.gpr _ (by simp), r6.gpr _ (by simp)]; exact hone k hk)
    (lim_lt (by decide) (by decide) (by decide) (by decide) (by decide))) fun s8 ⟨r8, f8, hS8⟩ => ?_
  refine ⟨⟨(hr1.mono (by decide)).trans ((r2.mono (by decide)).trans ((r3.mono (by decide)).trans
    ((r5.mono (by decide)).trans ((r6.mono (by decide)).trans ((r7.mono (by decide)).trans
    (r8.mono (by decide))))))), ?_⟩, hc7.of_rest r8 (by decide), ?_⟩
  · rw [← m1]
    refine f2.trans (f3.trans ?_)
    rw [← m5]
    exact f6.trans (f7.trans f8)
  · refine (hS8.mono (by decide)).congr fun q hq => ?_
    simp only [LQ, List.mem_cons, List.not_mem_nil, or_false] at hq
    rw [← hval]
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> rfl

end

/-! ## Five limbs to four words -/

/-- `pack` between its loads and its carry chain. -/
def packA : List Instr :=
  mask51 ++ [.li .r7 19] ++
  (List.range 4).flatMap (fun k =>
    [.lsr .d .r5 (ra k) 51, .logic .and (ra k) (ra k) .r4, .add (ra (k + 1)) (ra (k + 1)) .r5]) ++
  [.lsr .d .r5 .r18 51, .logic .and .r18 .r18 .r4, .mul .r5 .r5 .r7, .add .r14 .r14 .r5,
    .lsl .r5 .r15 51, .lsr .d .r9 .r15 13, .lsl .r12 .r16 38, .add .r9 .r9 .r12,
    .lsr .d .r10 .r16 26, .lsl .r12 .r17 25, .add .r10 .r10 .r12,
    .lsr .d .r11 .r17 39, .lsl .r12 .r18 12, .add .r11 .r11 .r12]

theorem pack_eq : pack = ldV ra X2 ++ (packA ++ (([.addc .r8 .r14 .r5, .addze .r9 .r9, .addze .r10 .r10,
    .addze .r11 .r11] : List Instr) ++ Impl.X25519.PPC64LE.stores4 O)) := by
  simp only [pack, packA, List.append_assoc, List.cons_append, List.nil_append]

theorem packA_ok {t : State} {l0 l1 l2 l3 l4 t1 t2 t3 t4 n0 m1 m2 m3 m4 x u1 u2 u3 : Nat}
    (h14 : (t.gpr .r14).toNat = l0) (h15 : (t.gpr .r15).toNat = l1) (h16 : (t.gpr .r16).toNat = l2)
    (h17 : (t.gpr .r17).toNat = l3) (h18 : (t.gpr .r18).toNat = l4)
    (b0 : l0 < 2 ^ 51 + 2 ^ 18) (b1 : l1 < 2 ^ 51 + 2 ^ 18) (b2 : l2 < 2 ^ 51 + 2 ^ 18)
    (b3 : l3 < 2 ^ 51 + 2 ^ 18) (b4 : l4 < 2 ^ 51 + 2 ^ 18)
    (ht1 : t1 = l1 + l0 / 2 ^ 51) (ht2 : t2 = l2 + t1 / 2 ^ 51) (ht3 : t3 = l3 + t2 / 2 ^ 51)
    (ht4 : t4 = l4 + t3 / 2 ^ 51) (hn0 : n0 = l0 % 2 ^ 51 + 19 * (t4 / 2 ^ 51))
    (hm1 : m1 = t1 % 2 ^ 51) (hm2 : m2 = t2 % 2 ^ 51) (hm3 : m3 = t3 % 2 ^ 51) (hm4 : m4 = t4 % 2 ^ 51)
    (hx : x = m1 * 2 ^ 51 % 2 ^ 64) (hu1 : u1 = (m1 / 2 ^ 13 + m2 * 2 ^ 38 % 2 ^ 64) % 2 ^ 64)
    (hu2 : u2 = (m2 / 2 ^ 26 + m3 * 2 ^ 25 % 2 ^ 64) % 2 ^ 64)
    (hu3 : u3 = (m3 / 2 ^ 39 + m4 * 2 ^ 12 % 2 ^ 64) % 2 ^ 64) :
    WP isa (.block packA) t fun s' => (s'.gpr .r14).toNat = n0 ∧ (s'.gpr .r5).toNat = x ∧
      (s'.gpr .r9).toNat = u1 ∧ (s'.gpr .r10).toNat = u2 ∧ (s'.gpr .r11).toNat = u3 ∧ s'.mem = t.mem := by
  subst hu3 hu2 hu1 hx hm4 hm3 hm2 hm1 hn0 ht4 ht3 ht2 ht1
  have a0 := tn_mask h14 m51
  have T1 := tn_add h15 (tn_shr h14 51) (by omega_using [b0, b1])
  have a1 := tn_mask T1 m51
  have T2 := tn_add h16 (tn_shr T1 51) (by omega_using [b0, b1, b2])
  have a2 := tn_mask T2 m51
  have T3 := tn_add h17 (tn_shr T2 51) (by omega_using [b0, b1, b2, b3])
  have a3 := tn_mask T3 m51
  have T4 := tn_add h18 (tn_shr T3 51) (by omega_using [b0, b1, b2, b3, b4])
  have a4 := tn_mask T4 m51
  have N0 := tn_add a0 (tn_mul19 (tn_shr T4 51) (by omega_using [b0, b1, b2, b3, b4]))
    (by omega_using [b0, b1, b2, b3, b4])
  have X := tn_shlm a1 51
  have U1 := tn_addm (tn_shr a1 13) (tn_shlm a2 38)
  have U2 := tn_addm (tn_shr a2 26) (tn_shlm a3 25)
  have U3 := tn_addm (tn_shr a3 39) (tn_shlm a4 12)
  crunr [packA, mask51, ra, List.range_succ, List.range_zero, List.flatMap_cons, List.flatMap_nil,
    List.nil_append, List.cons_append, List.append_assoc, List.getD_cons_zero, List.getD_cons_succ,
    List.getD_nil]
  exact ⟨N0, X, U1, U2, U3⟩

/-- The registers `pack` writes. -/
abbrev packRegs : List Reg := [.r4, .r5, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18]

theorem packA_writes : writesOnly packRegs (.block packA) = true := by decide +kernel

theorem pack_writes : writesOnly packRegs (.block pack) = true := by decide +kernel

section
variable {b : Addr}

/-- `pack`: the element at `X2`, as four words at `O`. -/
theorem pack_ok {s : State} (hc : Ctx b s) (ht : Tight s.mem b X2) :
    WP isa (.block pack) s fun s' => (V s'.mem b O % P = V5 s.mem b X2 % P ∧
      Frame [⟨b + BitVec.ofNat 64 O, 32⟩] s.mem s'.mem) ∧ Rest packRegs s s' := by
  refine WP.rest packRegs ?_ pack_writes
  rw [pack_eq]
  refine WP.append (ldV_ok opRegs_ra (by decide) (by decide) hc) fun s1 ⟨v1, r1, m1⟩ => ?_
  have hc1 := hc.of_rest r1 (by decide)
  refine WP.append (WP.rest packRegs (packA_ok (v1 0 (by decide)) (v1 1 (by decide)) (v1 2 (by decide))
    (v1 3 (by decide)) (v1 4 (by decide)) (ht 0 (by decide)) (ht 1 (by decide)) (ht 2 (by decide))
    (ht 3 (by decide)) (ht 4 (by decide)) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) packA_writes)
    fun s2 ⟨⟨N0, X, U1, U2, U3, m2⟩, r2⟩ => ?_
  have hc2 := hc1.of_rest r2 (by decide)
  refine wp_addc fun s3 u3 => wp_addze fun s4 u4 => wp_addze fun s5 u5 => wp_addze fun s6 u6 => ?_
  have e0 := u3.val; rw [N0, X] at e0
  have e1 := u4.val; rw [u3.other _ (by decide), U1] at e1
  have e2 := u5.val; rw [u4.other _ (by decide), u3.other _ (by decide), U2] at e2
  have e3 := u6.val; rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), U3] at e3
  have hv := pack_val (ht 0 (by decide)) (ht 1 (by decide)) (ht 2 (by decide)) (ht 3 (by decide))
    (ht 4 (by decide)) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl e0 e1 e2 e3
  have hc6 : Ctx b s6 := (((hc2.of_rest (u3.rest (ws := [.r8]) (by decide)) (by decide)).of_rest
    (u4.rest (ws := [.r9]) (by decide)) (by decide)).of_rest (u5.rest (ws := [.r10]) (by decide))
    (by decide)).of_rest (u6.rest (ws := [.r11]) (by decide)) (by decide)
  have m6 : s6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, m2, m1]
  refine WP.mono (stores4_ok (o := O) (by decide) (by decide) hc6) fun s7 ⟨hV, hf, _⟩ => ⟨?_, by
    rw [← m6]; exact hf⟩
  have e : rv4 s6 = (s3.gpr .r8).toNat + 2 ^ 64 * ((s4.gpr .r9).toNat + 2 ^ 64 * ((s5.gpr .r10).toNat +
      2 ^ 64 * (s6.gpr .r11).toNat)) := by
    show (s6.gpr .r8).toNat + 2 ^ 64 * ((s6.gpr .r9).toNat + 2 ^ 64 * ((s6.gpr .r10).toNat +
      2 ^ 64 * (s6.gpr .r11).toNat)) = _
    rw [u6.other .r8 (by decide), u5.other .r8 (by decide), u4.other .r8 (by decide),
      u6.other .r9 (by decide), u5.other .r9 (by decide), u6.other .r10 (by decide)]
  rw [hV, e, hv, V5]
  refine congrArg (· % P) (val5_congr fun k hk => ?_)
  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega_using [hk]
  rcases this with rfl | rfl | rfl | rfl | rfl <;> rfl

end

end VG.Proof.X25519.PPC64LE.Fe51

namespace VG.Proof.X25519.PPC64LE

open VG VG.PPC64LE VG.Impl.X25519.PPC64LE
open VG.Spec.X25519 (P Fe bytesAt)
open VG.Proof.X25519 (leBytes toFe ladderAfter ladderAfter_swap_le)

/-- `vg_x25519(out = r3, scalar = r4, point = r5, scratch = r6)`. -/
def x25519PPC64LE : Contract PPC64LE.isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, 32⟩
    let sc : Region := ⟨s.gpr .r4, 32⟩
    let pt : Region := ⟨s.gpr .r5, 32⟩
    let ws : Region := ⟨s.gpr .r6, 4096⟩
    s.rd = [sc, pt] ∧ s.wr = [out, ws] ∧ out.Disjoint sc ∧ out.Disjoint pt ∧ out.Disjoint ws ∧
      sc.Disjoint ws ∧ pt.Disjoint ws
  post s s' := bytesAt s'.mem (s.gpr .r3) 32 =
    VG.Spec.X25519.x25519 (bytesAt s.mem (s.gpr .r4) 32) (bytesAt s.mem (s.gpr .r5) 32)
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

theorem XPre.of {s : State} (h : x25519PPC64LE.pre s) : XPre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- `setup`: the decoded u-coordinate, as four words. -/
theorem setup_val {s : State} (hp : XPre s) :
    WP isa (.block setup) s fun s' =>
      Ctx (s.gpr .r6) s' ∧ Frame [⟨s.gpr .r6, 4096⟩] s.mem s'.mem ∧
      V s'.mem (s.gpr .r6) X1 = VG.Spec.X25519.decodeUCoordinate (bytesAt s.mem (s.gpr .r5) 32) ∧
      Rest [.r5, .r7, .r8] s s' := by
  have hX1 : X1 = 0 := rfl
  have hX2 : X2 = 32 := rfl
  have hZ2 : Z2 = 64 := rfl
  have hX3 : X3 = 96 := rfl
  have hZ3 : Z3 = 128 := rfl
  have hws : (⟨s.gpr .r6, 4096⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hc : Ctx (s.gpr .r6) s := ⟨rfl, 4096, Nat.le_refl _, hws⟩
  unfold setup
  refine WP.append (decode_ok hc (pt := s.gpr .r5) rfl (by rw [hp.rd]; simp) hp.pt_ws)
    fun s4 ⟨hl4, hf4, hr4⟩ => ?_
  have hc4 : Ctx (s.gpr .r6) s4 := hc.of_rest hr4 (by decide)
  refine WP.mono (consts_ok hc4) fun s5 ⟨_, _, _, hf5, hr5⟩ => ?_
  have e := limb_frame (o := X1) hf5 fun r hr j hj => by
    simp only [constsR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  refine ⟨hc4.of_rest hr5 (by decide), ?_, ?_, (hr4.mono (by decide)).trans (hr5.mono (by decide))⟩
  · have hsub : ∀ o n, o + n ≤ 4096 → Region.Sub ⟨s.gpr .r6 + BitVec.ofNat 64 o, n⟩
        ⟨s.gpr .r6, 4096⟩ := fun o n h => Offset.sub_base _ h
    refine (hf4.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact hsub _ _ (by omega_arith)⟩).trans ?_
    refine hf5.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [constsR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact hsub _ _ (by omega_arith)
  · rw [V, val32_congr fun k hk => (e k hk).trans (hl4 k hk).1, decode_val]

section
variable {b : Addr}

/-- An element's words stay through a write above them, `[lo, lo + n)`. -/
theorem V_above {m m' : Mem} {o lo n : Nat} (ho : o + 32 ≤ lo) (hn : lo + n ≤ 4096)
    (hf : Frame [⟨b + BitVec.ofNat 64 lo, n⟩] m m') : V m' b o = V m b o := by
  rw [V, V, val32_congr (limb_frame (o := o) hf fun r hr k hk => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl (by omega_using [ho, hk])) (by omega_using [hn, ho, hk])
      (by omega_using [hn]))]

/-- The bits stay through a write above them. -/
theorem Bits.above {m m' : Mem} {k : Nat} (h : Bits b k m) {lo n : Nat} (hlo : BITS + 255 ≤ lo)
    (hn : lo + n ≤ 4096) (hf : Frame [⟨b + BitVec.ofNat 64 lo, n⟩] m m') : Bits b k m' := fun t ht => by
  rw [hf _ fun r hr hc => (Offset.disjoint b (d := BITS + t) (n := 1) (e := lo) (k := n)
    (.inl (by omega_using [ht, hlo])) (by omega_using [ht, hlo, hn]) (by omega_using [hn])) _
    (Region.contains_self _ _) (by rw [List.mem_singleton.mp hr] at hc; exact hc)]
  exact h t ht

end

/-! ## The registers `x25519` saves -/

/-- The nonvolatile registers, and their slots. -/
def nvL : List (Reg × Nat) := (List.range 18).map fun k => (Fe51.nvR k, Fe51.SAVE + 8 * k)

theorem saveNV_eq : Fe51.saveNV = Spill.saveCode .r6 nvL := rfl

theorem restoreNV_eq : Fe51.restoreNV = Spill.restoreCode .r6 nvL := rfl

theorem nvL_ok : ∀ p ∈ nvL, p.2 % 8 = 0 ∧ p.2 < 32768 := by decide

theorem nvL_in : ∀ p ∈ nvL, SAVE ≤ p.2 ∧ p.2 + 8 ≤ SAVE + 144 := by decide

theorem nvL_fits : Spill.Fits nvL := by decide

theorem nvL_restorable : Spill.Restorable .r6 nvL := by decide

theorem nvL_regs : ∀ p ∈ nvL, p.1 ∉ clob ∧ p.1 ∉ [Reg.r4, .r7, .r8, .r9, .r11] ∧ p.1 ∉ [Reg.r5, .r7, .r8] ∧
    p.1 ≠ .r3 ∧ p.1 ≠ .r6 := by decide

theorem nvL_le {p : Reg × Nat} (hp : p ∈ nvL) : p.2 + 8 ≤ 4096 := by
  have := nvL_in p hp; have hS : SAVE = 896 := rfl; omega_using [this, hS]

theorem bytesAt_frame {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 32⟩ r) : bytesAt m' p 32 = bytesAt m p 32 := by
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  exact hf _ fun r hr hc => hd r hr _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) hc

theorem x25519_correct {s : State} (hp : XPre s) :
    WP isa Fe51.x25519 s fun s' => x25519PPC64LE.post s s' ∧ ∀ p ∈ nvL, s'.gpr p.1 = s.gpr p.1 := by
  have hB : BITS = 608 := rfl
  have hSV : SAVE = 896 := rfl
  have hsc_in : (⟨s.gpr .r4, 32⟩ : Region) ∈ s.rd ++ s.wr := by rw [hp.rd]; simp
  have hlt : VG.Spec.X25519.decodeUCoordinate (bytesAt s.mem (s.gpr .r5) 32) < 2 ^ 255 := by
    rw [VG.Proof.X25519.decodeUCoordinate_eq (length_bytesAt _ _ 32)]
    exact Nat.mod_lt _ (Nat.two_pow_pos 255)
  unfold Fe51.x25519
  rw [saveNV_eq, restoreNV_eq]
  refine WP.seq (WP.mono (setup_val hp) fun s1 ⟨hc1, hf1, hV1, hr1⟩ => ?_)
  refine WP.seq (WP.mono (bits_ok hc1 (hr1.gpr .r4 (by decide)) (by rw [hr1.rd, hr1.wr]; exact hsc_in)
    hp.sc_ws) fun s2 ⟨hc2, hr2, hf2, hb2⟩ => ?_)
  have hV2 := (V_above (o := X1) (lo := BITS) (by decide) (by decide) hf2).trans hV1
  -- The saves.
  refine WP.seq (WP.mono (Spill.save_wp (l := nvL) (by decide) nvL_ok
    (fun p hp => by rw [hc2.r6]; exact hc2.inW (nvL_le hp))) fun s3 hst => ?_)
  have hc3 : Ctx (s.gpr .r6) s3 := ⟨by rw [hst.gpr]; exact hc2.r6, by rw [hst.wr]; exact hc2.wr⟩
  have hfs : Frame [⟨s.gpr .r6 + BitVec.ofNat 64 SAVE, 144⟩] s2.mem s3.mem := by
    rw [hst.mem, hc2.r6]; exact Spill.saveMem_frame nvL_in (by decide) _ _ _
  have hsv : Spill.Saved (s.gpr .r6) s2.gpr nvL s3.mem := by
    rw [hst.mem, hc2.r6]; exact Spill.saveMem_saved nvL_fits _ _ _
  have hV3 := (V_above (o := X1) (lo := SAVE) (by decide) (by decide) hfs).trans hV2
  -- The ladder and the inversion, on five limbs.
  refine WP.seq (WP.mono (Fe51.unpack_ok hc3 hV3 hlt) fun s4 ⟨hst4, hc4, hS4⟩ => ?_)
  have hb4 := ((hb2.above (lo := SAVE) (by decide) (by decide) hfs).above (lo := 1088) (n := 640)
    (by decide) (by decide) hst4.frame)
  refine WP.seq (WP.mono (Fe51.ladder_ok hc4 hb4 hS4) fun s5 ⟨hst5, hc5, h0, hS5⟩ => ?_)
  refine WP.seq (WP.mono (Fe51.lastSwap_ok hc5 (ladderAfter_swap_le _ _ (by decide)) h0 hS5)
    fun s6 ⟨hst6, hc6, hS6⟩ => ?_)
  refine WP.seq (WP.mono (Fe51.invert_ok hc6 (hS6.mono (by decide)) rfl) fun s7 ⟨hst7, hc7, hS7⟩ => ?_)
  obtain ⟨-, tx, fx⟩ := hS7 Fe51.X2 (by decide)
  obtain ⟨-, tr, fr⟩ := hS7 Fe51.R (by decide)
  refine WP.seq (WP.mono (Fe51.mul_ok (o := Fe51.X2) (x := Fe51.X2) (y := Fe51.R) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hc7 tx tr) fun s8 ⟨hr8, hf8, t8, v8, _⟩ => ?_)
  have hc8 : Ctx (s.gpr .r6) s8 := hc7.of_rest hr8 (by decide)
  refine WP.seq (WP.mono (Fe51.pack_ok hc8 t8) fun s9 ⟨⟨hv9, hf9⟩, hr9⟩ => ?_)
  -- The registers and regions along the way.
  have hst8 : Fe51.Stp (s.gpr .r6) s3 s8 :=
    hst4.trans (hst5.trans (hst6.trans (hst7.trans ⟨hr8.mono (by decide), Fe51.frame_FB (by decide) hf8⟩)))
  have h3' : s9.gpr .r3 = s.gpr .r3 := by
    rw [hr9.gpr _ (by decide), hst8.rest.gpr _ (by decide), hst.gpr, hr2.gpr _ (by decide),
      hr1.gpr _ (by decide)]
  have hwr9 : s9.wr = s.wr := by rw [hr9.wr, hst8.rest.wr, hst.wr, hr2.wr, hr1.wr]
  have hc9 : Ctx (s.gpr .r6) s9 := hc8.of_rest hr9 (by decide)
  have hsv9 : Spill.Saved (s.gpr .r6) s2.gpr nvL s9.mem :=
    (hsv.frame_in nvL_in hst8.frame fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl (by omega_using [hSV])) (by omega_using [hSV]) (by decide)).frame_in
      nvL_in hf9 fun r hr => by
        rw [List.mem_singleton.mp hr]
        have hO : Fe51.O = 32 := rfl
        exact Offset.disjoint _ (.inr (by omega_using [hSV, hO])) (by omega_using [hSV]) (by decide)
  -- The restores.
  refine Spill.restore_ok (by decide) hc9.r6 nvL_ok nvL_restorable (fun p hp => hc9.inR (nvL_le hp)) hsv9
    fun s10 hR => ?_
  have hc10 : Ctx (s.gpr .r6) s10 :=
    ⟨by rw [hR.other _ (by decide)]; exact hc9.r6, by rw [hR.wr]; exact hc9.wr⟩
  have h3'' : s10.gpr .r3 = s.gpr .r3 := by rw [hR.other _ (by decide), h3']
  refine WP.mono (freeze_ok hc10 h3'' (by rw [hR.wr, hwr9, hp.wr]; simp) hp.out_ws.symm)
    fun s11 ⟨hbytes, hr11, _⟩ => ⟨?_, fun p hp => ?_⟩
  -- The result.
  · show bytesAt s11.mem _ 32 = _
    rw [hbytes, hR.mem, show V s9.mem (s.gpr .r6) X2 % P = _ from hv9, VG.Proof.X25519.x25519_eq]
    -- The scalar, as read by `bits`.
    have hk : bytesAt s1.mem (s.gpr .r4) 32 = bytesAt s.mem (s.gpr .r4) 32 :=
      bytesAt_frame hf1 fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.sc_ws
    rw [hk] at hS5 h0 hS6 hS7 fx fr
    rw [← VG.Proof.X25519.toFe_val, ← VG.Proof.X25519.encodeUCoordinate_eq]
    change VG.Spec.X25519.encodeUCoordinate (Fe51.FS s8.mem (s.gpr .r6) Fe51.X2) = _
    rw [v8, fx, fr]
    simp only [Fe51.upd, Fe51.swapV, Fe51.ladV, VG.Proof.X25519.invert_eq, VG.Proof.X25519.pow_pw, cswap_fst,
      Fe51.X1, Fe51.X2, Fe51.Z2, Fe51.X3, Fe51.Z3, Fe51.R, Nat.reduceEqDiff, ite_false, ite_true]
  -- The saved registers.
  · obtain ⟨n1, n2, n3, -, -⟩ := nvL_regs p hp
    rw [hr11.gpr _ n1, hR.gpr p hp, hr2.gpr _ n2, hr1.gpr _ n3]

end VG.Proof.X25519.PPC64LE

/-!
# X25519 on PPC64LE: verified

`vg_x25519` meets the shared contract of `Spec/X25519/Contract.lean`: the
proof against `x25519PPC64LE`, which it implies, and a state satisfying it.
The code restores the nonvolatile registers it uses (`x25519_correct`),
writes no other, and never writes the link register or calls a function, so
the ABI's obligations hold of every execution.
-/

namespace VG.Proof.X25519.PPC64LE

open VG VG.PPC64LE

theorem x25519_ok (s : State) (hs : x25519PPC64LE.pre s) :
    ∃ t s', Exec isa Impl.X25519.PPC64LE.Fe51.x25519 s t s' ∧ abiPreserved s s' ∧
      x25519PPC64LE.post s s' := by
  obtain ⟨t, s', he, h, hnv⟩ := x25519_correct (XPre.of hs)
  have hd : ∀ r ∈ [Reg.r2], ∀ i ∈ instrs Impl.X25519.PPC64LE.Fe51.x25519, dstOf i ≠ some r :=
    nv_of_avoids (by decide +kernel)
  have hpre : ∀ r ∈ preserved, r ∈ [Reg.r2] ∨ ∃ p ∈ nvL, p.1 = r := by decide
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he,
    Exec.lr he (by decide +kernel) (by rw [← Code.allInstrs_eq]; decide +kernel)⟩, h⟩
  rcases hpre r hr with h2 | ⟨p, hp, rfl⟩
  · exact Exec.gpr (hd _ h2) he (.inl (by decide +kernel))
  · exact hnv p hp

theorem x25519_ct' :
    ConstantTime isa x25519PPC64LE.pre x25519PPC64LE.pub Impl.X25519.PPC64LE.Fe51.x25519 :=
  x25519_ct fun _ _ _ _ ⟨h3, h4, h5, h6, hsp⟩ => ⟨hsp, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption⟩

/-- A state satisfying the precondition. -/
def x25519Sat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x4000 | _ => 0
  lr := 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 4096⟩]

theorem x25519_verified :
    Verified PPC64LE.target Impl.X25519.PPC64LE.Fe51.x25519 (Proof.X25519.x25519Contract PPC64LE.abi) :=
  Verified.of_correct x25519_ok x25519_ct' (by
    contract_implies [Proof.X25519.x25519Contract, Proof.X25519.x25519Sig, Proof.X25519.PPC64LE.x25519PPC64LE,
      PPC64LE.abi, PPC64LE.argRegs] [Proof.X25519.PPC64LE.x25519Sat] using Proof.X25519.PPC64LE.x25519Sat)

end VG.Proof.X25519.PPC64LE

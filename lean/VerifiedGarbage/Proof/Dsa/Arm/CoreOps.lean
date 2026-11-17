module

public import VerifiedGarbage.Proof.Dsa.Arm.Pow
public import VerifiedGarbage.Impl.Dsa.Arm.Core
public import VerifiedGarbage.Proof.Dsa.Arm.ArithCall
import VerifiedGarbage.Proof.Dsa.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Encoding
public import VerifiedGarbage.Impl.Dsa.Arm.Bytes
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Zeros
import VerifiedGarbage.Proof.Weierstrass.BytesLen32
import VerifiedGarbage.Proof.Weierstrass.Words
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Ws
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! ### `Dsa.Arm.Bytes`, which this module and modules that import it used -/

section

/-!
# DSA on 32-bit ARM: big-endian components

`loadComponent len n out` reads the `len` big-endian bytes at `r11` into the
`2n` words at `[out]` (`loadComponent_ok`), a byte-reversed word a step from
the last, and zeros the words past `len`; `storeComponent len input` writes
`[input]`, masked with `r3`, to the `len` bytes at `r11`
(`storeComponent_ok`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_str wp_ldr wp_dp wp_movw op2_imm op2_reg)

theorem wp_rev {s : State} {is : List Instr} {Q : State → Prop} {d m : Reg}
    (k : ∀ s', Upd s s' d (byteRev32 (s.gpr m)) → WP isa (.block is) s' Q) :
    WP isa (.block (.rev d m :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem readW32_keep {m m' : Mem} {p : Addr} {d : Nat}
    (h : ∀ i < 4, m' (p + BitVec.ofNat 64 (d + i)) = m (p + BitVec.ofNat 64 (d + i))) :
    m'.readW (p + BitVec.ofNat 64 d) 32 = m.readW (p + BitVec.ofNat 64 d) 32 :=
  Mem.readW_congr fun i hi => by rw [Offset.add_add, h i hi]

theorem decodeBE_ofBytes (bs : List Byte) : Spec.Dsa.decodeBE bs = Spec.Weierstrass.ofBytes bs := rfl

theorem rsa_bytesAt (m : Mem) (p : Addr) (n : Nat) : Spec.Rsa.bytesAt m p n = Spec.Ecdsa.bytesAt m p n := rfl

/-- `r8` after `j` words: `len - 4 (j + 1)` bytes into the component. -/
theorem r8_at {e x : BitVec 32} {len j : Nat} (h : x + BitVec.ofNat 32 (4 * j) = e + BitVec.ofNat 32 (len - 4))
    (hj : 4 * (j + 1) ≤ len) : x = e + BitVec.ofNat 32 (len - 4 * (j + 1)) := by
  obtain h' := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq
  have := x.isLt; have := e.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h' ⊢
  omega_arith

/-- `r8` a word lower. -/
theorem r8_down {x e : BitVec 32} {j : Nat} (h : x + BitVec.ofNat 32 (4 * j) = e) :
    x - BitVec.ofNat 32 4 + BitVec.ofNat 32 (4 * (j + 1)) = e := by
  rw [← h]
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_arith

/-- Zero words from `[r10 + 4c]`. -/
theorem zeroPadInline_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {o K : Nat}
    (h10 : s.gpr .r10 = s.gpr .r12 + BitVec.ofNat 32 o) (hK : o + 4 * K ≤ size) (hK4 : 4 * K ≤ 4096) :
    ∀ k ≤ K, WP isa (.block ((List.range k).flatMap fun j => [.mov .r4 (.imm 0), .str .r4 .r10 (4 * j)])) s
      fun u => Ws u base size ∧ (∀ j < k, w32 u.mem base (o + 4 * j) = 0) ∧ Rest [.r4] s u ∧
        Outside base o (4 * k) s.mem u.mem
  | 0, _ => WP.block_nil ⟨hs, fun _ h => absurd h (Nat.not_lt_zero _), Rest.refl _ _, Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine VG.Proof.X25519.Arm.WP.append (zeroPadInline_ok hs h10 hK hK4 k (by omega_arith)) fun s₁ ⟨w₁, e₁, R₁, O₁⟩ => ?_
    refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => ?_
    obtain w₂ := w₁.of_upd u₂ (by decide)
    refine wp_str (by omega_arith) (w₂.ea (K := o) (d := 4 * k) (by
      rw [u₂.other .r10 (by decide), u₂.other .r12 (by decide), R₁.gpr .r10 (by decide), R₁.gpr .r12 (by decide)]
      exact h10) (by omega_arith)) (w₂.write (d := o + 4 * k) (n := 4) (by omega_arith)) fun s₃ m₃ => WP.block_nil ?_
    obtain O₂ : Outside base (o + 4 * k) 4 s₁.mem s₃.mem := by
      rw [m₃.mem, u₂.mem]; exact writeW32_outside _ _ _ (by omega_arith)
    refine ⟨w₂.of_mupd m₃, fun j hj => ?_, R₁.trans ((u₂.rest (by decide)).trans (m₃.rest _)),
      (O₁.mono (Nat.le_refl _) (by omega_arith)).trans (O₂.mono (by omega_arith) (by omega_arith))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [O₂.w32 (by omega_arith) (by omega_arith), e₁ j h]
    · obtain rfl : j = k := by omega_arith
      rw [m₃.mem, u₂.mem, w32_write_self, u₂.gpr]; rfl

theorem zeroPadLoop_ok {s : State} {base : Addr} {size o k : Nat} (hs : Ws s base size)
    (h10 : s.gpr .r10 = s.gpr .r12 + BitVec.ofNat 32 o)
    (hk : 0 < k) (hok : o + 4 * k ≤ size) (h16 : 4 * k < 2 ^ 16) :
    WP isa (zeroPadLoop k) s fun t => Ws t base size ∧ (∀ j < k, w32 t.mem base (o + 4 * j) = 0) ∧
      Outside base o (4 * k) s.mem t.mem ∧ Rest [.r4, .r9, .r10] s t := by
  have hn := hs.nowrap
  unfold zeroPadLoop
  refine WP.seq (wp_movw fun s₁ u₁ => wp_dp (op2_reg _ _) fun s₂ u₂ =>
    wp_mov (op2_imm (by decide)) fun t u₃ => WP.block_nil ?_)
  obtain R : Rest [.r4, .r9, .r10] s t :=
    ((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans (u₃.rest (by decide))
  obtain wt : Ws t base size := hs.of_rest R (by decide)
  have r4 : t.gpr .r4 = 0 := u₃.gpr
  obtain mt : t.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain p0 : t.gpr .r10 = s.gpr .r12 + BitVec.ofNat 32 o := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]; exact h10
  obtain p9 : t.gpr .r9 = s.gpr .r12 + BitVec.ofNat 32 (o + 4 * k) := by
    rw [u₃.other _ (by decide), u₂.gpr, VG.Proof.X25519.Arm.dpVal, u₁.gpr,
      u₁.other .r10 (by decide), h10, movw_ofNat h16, Offset.add_add]
  clear u₁ u₂ u₃
  refine ptrLoop_ok (A := s.gpr .r12 + BitVec.ofNat 32 o) (step := 4) (k := k)
    (fun j u => Ws u base size ∧ u.gpr .r4 = 0 ∧ Rest [.r4, .r9, .r10] s u ∧
      (∀ i < j, w32 u.mem base (o + 4 * i) = 0) ∧ Outside base o (4 * k) s.mem u.mem)
    (by decide) hk (by omega_arith) (fun j u u' ⟨a, b, c, d, e⟩ f => ⟨a.of_fupd f, by rw [f.gpr]; exact b,
      c.trans (f.rest _), by rw [f.mem]; exact d, by rw [f.mem]; exact e⟩)
    ⟨wt, r4, R, fun i hi => absurd hi (Nat.not_lt_zero _), by rw [mt]; exact Outside.refl _ _ _ _⟩
    p0 (by rw [p9, Offset.add_add]) ?_ fun u ⟨a, _, c, d, e⟩ _ => ⟨a, d, e, c⟩
  intro j hj u ⟨wu, r4u, Ru, Vu, Ou⟩ pu p9u
  obtain e12 : u.gpr .r12 = s.gpr .r12 := Ru.gpr _ (by decide)
  refine wp_str (by decide) (wu.ea (K := o + 4 * j) (at_ptr pu e12) (by omega_arith)) (wu.write (d := o + 4 * j + 0) (n := 4) (by omega_arith))
    fun u₁ m₁ => wp_bump (by decide) fun u₂ v₂ => WP.block_nil ⟨⟨wu.of_mupd m₁ |>.of_upd v₂ (by decide), ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [v₂.other .r4 (by decide), m₁.gpr]; exact r4u
  · exact (Ru.trans (m₁.rest _)).trans (v₂.rest (by simp))
  · intro i hi
    rw [v₂.mem, m₁.mem]
    rcases Nat.lt_or_ge i j with h | h
    · rw [w32_write_lt (by omega_arith) (by omega_arith), Vu i h]
    · rw [show i = j by omega_arith, Nat.add_zero, w32_write_self, r4u]; rfl
  · rw [v₂.mem, m₁.mem]; exact Ou.write32 (by omega_arith) (by omega_arith) (by omega_arith) _
  · rw [v₂.gpr, m₁.gpr, pu, Offset.add_add, Offset.add_add, Offset.add_add]; congr 2
  · rw [v₂.other .r9 (by decide), m₁.gpr]; exact p9u

theorem zeroPad_ok {s : State} {base : Addr} {size o k : Nat} (hs : Ws s base size)
    (h10 : s.gpr .r10 = s.gpr .r12 + BitVec.ofNat 32 o)
    (hz : o + 4 * k ≤ size) (h4 : 4 * k ≤ 4096) :
    WP isa (zeroPad k) s fun t => Ws t base size ∧ (∀ j < k, w32 t.mem base (o + 4 * j) = 0) ∧
      Rest [.r4, .r9, .r10] s t ∧ Outside base o (4 * k) s.mem t.mem := by
  unfold zeroPad
  split
  · exact WP.mono (zeroPadInline_ok hs h10 hz h4 k (Nat.le_refl _))
      fun _ ⟨W, V, R, O⟩ => ⟨W, V, R.mono (by decide), O⟩
  · exact WP.mono (zeroPadLoop_ok hs h10 (by omega_arith) hz (by omega_arith))
      fun _ ⟨W, V, O, R⟩ => ⟨W, V, R, O⟩

/-- `[out] = ` the `len` big-endian bytes at `r11`, `2n` words. -/
theorem loadComponent_ok {s : State} {base : Addr} {size len n out : Nat} (hs : Ws s base size)
    (ho : out + 8 * n ≤ size) (h16 : out + len < 2 ^ 16) (hpad : 8 * n ≤ len + 4096)
    (hp : (s.gpr .r11).toNat + len ≤ 2 ^ 32) (h4 : 4 ≤ len) (hlen : len ≤ 8 * n) (hw4 : len % 4 = 0)
    (hr : ∀ d, d + 4 ≤ len → InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r11) + BitVec.ofNat 64 d) 4)
    (hd : Region.Disjoint ⟨State.addr (s.gpr .r11), len⟩ ⟨off base out, 8 * n⟩) :
    WP isa (loadComponent len n out) s fun t => Ws t base size ∧
      val32 t.mem base out (2 * n) = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r11)) len) ∧
      Rest [.r4, .r8, .r9, .r10] s t ∧ Outside base out (8 * n) s.mem t.mem := by
  have hn := hs.nowrap
  let P := State.addr (s.gpr .r11)
  obtain hP : P.toNat = (s.gpr .r11).toNat := VG.Proof.X25519.Arm.addr_toNat _
  unfold loadComponent
  refine WP.seq (wp_movw fun s₀ u₀ => wp_dp (op2_reg _ _) fun s₁ u₁ =>
    wp_ptr (d := .r10) (by decide) (by omega_arith) fun s₂ u₂ => wp_ptr (d := .r9) (by decide) (by omega_arith) fun t u₃ =>
    WP.block_nil ?_)
  obtain R : Rest [.r4, .r8, .r9, .r10] s t := ((u₀.rest (by decide)).trans (u₁.rest (by decide))).trans
    ((u₂.rest (by decide)).trans (u₃.rest (by decide)))
  obtain mt : t.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem, u₀.mem]
  obtain r8 : t.gpr .r8 = s.gpr .r11 + BitVec.ofNat 32 (len - 4) := by
    simp only [u₃.get, u₂.get, u₁.get, u₀.get, reduceCtorEq, ↓reduceIte, VG.Proof.X25519.Arm.dpVal]
    rw [movw_ofNat (by omega_arith)]
  obtain p10 : t.gpr .r10 = s.gpr .r12 + BitVec.ofNat 32 out := by
    simp only [u₃.get, u₂.get, u₁.get, u₀.get, reduceCtorEq, ↓reduceIte]
  obtain p9 : t.gpr .r9 = s.gpr .r12 + BitVec.ofNat 32 out + BitVec.ofNat 32 (4 * (len / 4)) := by
    simp only [u₃.get, u₂.get, u₁.get, u₀.get, reduceCtorEq, ↓reduceIte, Offset.add_add]
    rw [show 4 * (len / 4) = len by omega_arith]
  clear u₀ u₁ u₂ u₃
  refine WP.seq (ptrLoop_ok (A := s.gpr .r12 + BitVec.ofNat 32 out) (step := 4) (k := len / 4)
    (fun j u => Ws u base size ∧ Rest [.r4, .r8, .r9, .r10] s u ∧
      u.gpr .r8 + BitVec.ofNat 32 (4 * j) = s.gpr .r11 + BitVec.ofNat 32 (len - 4) ∧
      Outside base out (4 * j) s.mem u.mem ∧ ∀ i < j, w32 u.mem base (out + 4 * i) = VG.Proof.Weierstrass.ldWord32 s.mem P len i)
    (by decide) (by omega_arith) (by omega_arith)
    (fun j u u' ⟨a, b, c, d, e⟩ F => ⟨a.of_fupd F, b.trans (F.rest _), by rw [F.gpr]; exact c,
      by rw [F.mem]; exact d, by rw [F.mem]; exact e⟩)
    ⟨hs.of_rest R (by decide), R, by rw [r8, Nat.mul_zero]; exact BitVec.add_zero _,
      by rw [mt]; exact Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
    p10 p9 ?_ fun u I pu => ?_)
  · intro j hj u ⟨wu, Ru, e8, Ou, Vu⟩ pu p9u
    obtain e12 : u.gpr .r12 = s.gpr .r12 := Ru.gpr _ (by decide)
    obtain r8u : u.gpr .r8 = s.gpr .r11 + BitVec.ofNat 32 (len - 4 * (j + 1)) := r8_at e8 (by omega_arith)
    obtain ha : State.addr (u.gpr .r8 + BitVec.ofNat 32 0) = P + BitVec.ofNat 64 (len - 4 * (j + 1)) := by
      rw [BitVec.add_zero, r8u]; exact VG.Arm.addr_add (by omega_arith)
    obtain hrd : InRegions (u.rd ++ u.wr) (P + BitVec.ofNat 64 (len - 4 * (j + 1))) 4 := by
      rw [Ru.rd, Ru.wr]; exact hr _ (by omega_arith)
    obtain hkeep : u.mem.readW (P + BitVec.ofNat 64 (len - 4 * (j + 1))) 32 =
        s.mem.readW (P + BitVec.ofNat 64 (len - 4 * (j + 1))) 32 :=
      readW32_keep fun i hi => VG.Proof.Weierstrass.keep_of_disjoint (Ou.mono (Nat.le_refl _) (by omega_arith)) hd
        (by omega_arith) (by omega_arith) (by omega_arith)
    refine wp_ldr (by decide) ha hrd fun u₁ v₁ => wp_rev fun u₂ v₂ => ?_
    obtain w₂ := (wu.of_upd v₁ (by decide)).of_upd v₂ (by decide)
    refine wp_str (by decide) (w₂.ea (K := out + 4 * j) (d := 0) (at_ptr (by
      rw [v₂.other .r10 (by decide), v₁.other .r10 (by decide)]; exact pu)
      (by rw [v₂.other .r12 (by decide), v₁.other .r12 (by decide)]; exact e12)) (by omega_arith))
      (w₂.write (d := out + 4 * j + 0) (n := 4) (by omega_arith)) fun u₃ m₃ => ?_
    refine wp_dp (VG.Proof.X25519.Arm.op2_imm (encodable_lt (n := 4) (by decide))) fun u₄ v₄ =>
      wp_bump (by decide) fun u₅ v₅ => WP.block_nil ?_
    obtain O₂ : Outside base (out + 4 * j) 4 u.mem u₃.mem := by
      rw [m₃.mem, v₂.mem, v₁.mem, Nat.add_zero]; exact writeW32_outside _ _ _ (by omega_arith)
    obtain m₅ : u₅.mem = u₃.mem := by rw [v₅.mem, v₄.mem]
    refine ⟨⟨(((w₂.of_mupd m₃).of_upd v₄ (by decide)).of_upd v₅ (by decide)),
      Ru.trans ((((v₁.rest (by decide)).trans (v₂.rest (by decide))).trans (m₃.rest _)).trans
        ((v₄.rest (by decide)).trans (v₅.rest (by decide)))), ?_, ?_, fun i hi => ?_⟩, ?_, ?_⟩
    · rw [v₅.other .r8 (by decide), v₄.gpr, m₃.gpr, v₂.other .r8 (by decide), v₁.other .r8 (by decide)]
      exact r8_down e8
    · rw [m₅]; exact (Ou.mono (Nat.le_refl _) (by omega_arith)).trans (O₂.mono (by omega_arith) (by omega_arith))
    · rw [m₅]
      rcases Nat.lt_or_ge i j with h | h
      · rw [O₂.w32 (by omega_arith) (by omega_arith), Vu i h]
      · obtain rfl : i = j := by omega_arith
        rw [m₃.mem, v₂.mem, v₁.mem, Nat.add_zero, w32_write_self, v₂.gpr, v₁.gpr, hkeep, VG.Proof.Weierstrass.ldWord32,
          ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith))]
    · rw [v₅.gpr, v₄.other .r10 (by decide), m₃.gpr, v₂.other .r10 (by decide), v₁.other .r10 (by decide)]
      exact ptr_step pu
    · rw [v₅.other .r9 (by decide), v₄.other .r9 (by decide), m₃.gpr, v₂.other .r9 (by decide),
        v₁.other .r9 (by decide)]
      exact p9u
  · obtain ⟨wu, Ru, _, Ou, Vu⟩ := I
    obtain e12 : u.gpr .r12 = s.gpr .r12 := Ru.gpr _ (by decide)
    refine WP.mono (zeroPad_ok wu (o := out + len) (k := 2 * n - len / 4)
      (by rw [pu, e12, Offset.add_add, show out + 4 * (len / 4) = out + len by omega_arith]) (by omega_arith) (by omega_arith)) fun t ⟨wt, Z, R₂, O₂⟩ => ⟨wt, ?_, Ru.trans (R₂.mono (by decide)), ?_⟩
    · rw [decodeBE_ofBytes, rsa_bytesAt]
      refine VG.Proof.Weierstrass.val32_eq_ofBytes_len _ _ _ _ out (2 * n) len h4 (by omega_arith) fun j hj => ?_
      rcases Nat.lt_or_ge j (len / 4) with h | h
      · rw [O₂.w32 (by omega_arith) (by omega_arith), Vu j h]
      · rw [show out + 4 * j = out + len + 4 * (j - len / 4) by omega_arith, Z _ (by omega_arith),
          VG.Proof.Weierstrass.ldWord32, ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith)),
          ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith))]
    · exact (Ou.mono (Nat.le_refl _) (by omega_arith)).trans (O₂.mono (by omega_arith) (by omega_arith))

theorem toBytes_encodeBE (n x : Nat) : Spec.Weierstrass.toBytes n x = Spec.Dsa.encodeBE n x := by
  apply List.ext_getElem
  · simp only [Spec.Weierstrass.toBytes, Spec.Dsa.encodeBE, List.length_map, List.length_reverse, List.length_range]
  · intro i hi hj
    simp only [Spec.Weierstrass.toBytes, Spec.Dsa.encodeBE, List.getElem_map, List.getElem_reverse,
      List.length_range, List.getElem_range]

/-- The `len` big-endian bytes at `r11` = `[input]` (its `len / 4` words) masked with `r3`. -/
theorem storeComponent_ok {s : State} {base : Addr} {size len input : Nat} (hs : Ws s base size) (accepted : Bool)
    (hc : s.gpr .r3 = if accepted then BitVec.allOnes 32 else 0)
    (hin : input + len ≤ size) (h16 : input + len < 2 ^ 16) (h4 : 4 ≤ len) (hw4 : len % 4 = 0)
    (hp : (s.gpr .r11).toNat + len ≤ 2 ^ 32)
    (hw : ∀ e k, e + k ≤ len → InRegions s.wr (State.addr (s.gpr .r11) + BitVec.ofNat 64 e) k)
    (hd : Region.Disjoint ⟨off base input, len⟩ ⟨State.addr (s.gpr .r11), len⟩) :
    WP isa (storeComponent len input) s fun t => Ws t base size ∧
      Spec.Rsa.bytesAt t.mem (State.addr (s.gpr .r11)) len =
        (if accepted then Spec.Dsa.encodeBE len (val32 s.mem base input (len / 4)) else List.replicate len 0) ∧
      Rest [.r4, .r8, .r9, .r10] s t ∧ Outside (State.addr (s.gpr .r11)) 0 len s.mem t.mem := by
  have hn := hs.nowrap
  let P := State.addr (s.gpr .r11)
  obtain hP : P.toNat = (s.gpr .r11).toNat := VG.Proof.X25519.Arm.addr_toNat _
  let mask : BitVec 32 := if accepted then BitVec.allOnes 32 else 0
  unfold storeComponent
  refine WP.seq (wp_movw fun s₀ u₀ => wp_dp (op2_reg _ _) fun s₁ u₁ =>
    wp_ptr (d := .r10) (by decide) (by omega_arith) fun s₂ u₂ => wp_ptr (d := .r9) (by decide) (by omega_arith) fun t u₃ =>
    WP.block_nil ?_)
  obtain R : Rest [.r4, .r8, .r9, .r10] s t := ((u₀.rest (by decide)).trans (u₁.rest (by decide))).trans
    ((u₂.rest (by decide)).trans (u₃.rest (by decide)))
  obtain mt : t.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem, u₀.mem]
  obtain r8 : t.gpr .r8 = s.gpr .r11 + BitVec.ofNat 32 (len - 4) := by
    simp only [u₃.get, u₂.get, u₁.get, u₀.get, reduceCtorEq, ↓reduceIte, VG.Proof.X25519.Arm.dpVal]
    rw [movw_ofNat (by omega_arith)]
  obtain p10 : t.gpr .r10 = s.gpr .r12 + BitVec.ofNat 32 input := by
    simp only [u₃.get, u₂.get, u₁.get, u₀.get, reduceCtorEq, ↓reduceIte]
  obtain p9 : t.gpr .r9 = s.gpr .r12 + BitVec.ofNat 32 input + BitVec.ofNat 32 (4 * (len / 4)) := by
    simp only [u₃.get, u₂.get, u₁.get, u₀.get, reduceCtorEq, ↓reduceIte, Offset.add_add]
    rw [show 4 * (len / 4) = len by omega_arith]
  clear u₀ u₁ u₂ u₃
  obtain hPl : P.toNat + len ≤ 2 ^ 64 := by omega_arith
  refine ptrLoop_ok (A := s.gpr .r12 + BitVec.ofNat 32 input) (step := 4) (k := len / 4)
    (fun j u => Ws u base size ∧ Rest [.r4, .r8, .r9, .r10] s u ∧
      u.gpr .r8 + BitVec.ofNat 32 (4 * j) = s.gpr .r11 + BitVec.ofNat 32 (len - 4) ∧
      Outside P (len - 4 * j) (4 * j) s.mem u.mem ∧
      ∀ i < j, u.mem.readW (P + BitVec.ofNat 64 (len - 4 * (i + 1))) 32 =
        byteRev32 (s.mem.readW (off base (input + 4 * i)) 32 &&& mask))
    (by decide) (by omega_arith) (by omega_arith)
    (fun j u u' ⟨a, b, c, d, e⟩ F => ⟨a.of_fupd F, b.trans (F.rest _), by rw [F.gpr]; exact c,
      by rw [F.mem]; exact d, by rw [F.mem]; exact e⟩)
    ⟨hs.of_rest R (by decide), R, by rw [r8, Nat.mul_zero]; exact BitVec.add_zero _,
      by rw [mt]; exact Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
    p10 p9 ?_ fun u ⟨wu, Ru, _, Ou, Vu⟩ _ => ⟨wu, ?_, Ru, ?_⟩
  · intro j hj u ⟨wu, Ru, e8, Ou, Vu⟩ pu p9u
    obtain e12 : u.gpr .r12 = s.gpr .r12 := Ru.gpr _ (by decide)
    obtain r8u : u.gpr .r8 = s.gpr .r11 + BitVec.ofNat 32 (len - 4 * (j + 1)) := r8_at e8 (by omega_arith)
    obtain hword : u.mem.readW (off base (input + 4 * j + 0)) 32 = s.mem.readW (off base (input + 4 * j)) 32 := by
      rw [Nat.add_zero]
      show u.mem.readW (base + BitVec.ofNat 64 (input + 4 * j)) 32 = s.mem.readW (base + BitVec.ofNat 64 (input + 4 * j)) 32
      rw [← Offset.add_add]
      exact readW32_keep fun i hi => VG.Proof.Weierstrass.keep_of_disjoint' (Ou.mono (Nat.zero_le _) (by omega_arith)) hd
        (by omega_arith) (by omega_arith) (by omega_arith)
    refine wp_ldr (by decide) (wu.ea (K := input + 4 * j) (d := 0) (at_ptr pu e12) (by omega_arith))
      (wu.read (d := input + 4 * j + 0) (n := 4) (by omega_arith)) fun u₁ v₁ => ?_
    refine wp_dp (op2_reg _ _) fun u₂ v₂ => wp_rev fun u₃ v₃ => ?_
    obtain w₃ := ((wu.of_upd v₁ (by decide)).of_upd v₂ (by decide)).of_upd v₃ (by decide)
    obtain ha₃ : State.addr (u₃.gpr .r8 + BitVec.ofNat 32 0) = P + BitVec.ofNat 64 (len - 4 * (j + 1)) := by
      rw [BitVec.add_zero, v₃.other .r8 (by decide), v₂.other .r8 (by decide), v₁.other .r8 (by decide), r8u]
      exact VG.Arm.addr_add (by omega_arith)
    obtain hw₃ : InRegions u₃.wr (P + BitVec.ofNat 64 (len - 4 * (j + 1))) 4 := by
      rw [v₃.wr, v₂.wr, v₁.wr, Ru.wr]; exact hw _ _ (by omega_arith)
    refine wp_str (by decide) ha₃ hw₃ fun u₄ m₄ => ?_
    refine wp_dp (VG.Proof.X25519.Arm.op2_imm (encodable_lt (n := 4) (by decide))) fun u₅ v₅ =>
      wp_bump (by decide) fun u₆ v₆ => WP.block_nil ?_
    obtain v₃' : u₃.gpr .r4 = byteRev32 (s.mem.readW (off base (input + 4 * j)) 32 &&& mask) := by
      rw [v₃.gpr, v₂.gpr, VG.Proof.X25519.Arm.dpVal, v₁.gpr, v₁.other .r3 (by decide), Ru.gpr .r3 (by decide), hc,
        hword]
    obtain mem₃ : u₃.mem = u.mem := by rw [v₃.mem, v₂.mem, v₁.mem]
    obtain O₂ : Outside P (len - 4 * (j + 1)) 4 u.mem u₄.mem := by
      rw [m₄.mem, mem₃]; exact writeW32_outside _ _ _ (by omega_arith)
    obtain m₆ : u₆.mem = u₄.mem := by rw [v₆.mem, v₅.mem]
    refine ⟨⟨(((w₃.of_mupd m₄).of_upd v₅ (by decide)).of_upd v₆ (by decide)),
      Ru.trans ((((v₁.rest (by decide)).trans (v₂.rest (by decide))).trans ((v₃.rest (by decide)).trans
        (m₄.rest _))).trans ((v₅.rest (by decide)).trans (v₆.rest (by decide)))), ?_, ?_, fun i hi => ?_⟩, ?_, ?_⟩
    · rw [v₆.other .r8 (by decide), v₅.gpr, m₄.gpr, v₃.other .r8 (by decide), v₂.other .r8 (by decide),
        v₁.other .r8 (by decide)]
      exact r8_down e8
    · rw [m₆]; exact (Ou.mono (by omega_arith) (by omega_arith)).trans (O₂.mono (by omega_arith) (by omega_arith))
    · rw [m₆]
      rcases Nat.lt_or_ge i j with h | h
      · rw [m₄.mem, mem₃, Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide), Vu i h]
      · obtain rfl : i = j := by omega_arith
        rw [m₄.mem, Mem.readW_writeW_self32, v₃']
    · rw [v₆.gpr, v₅.other .r10 (by decide), m₄.gpr, v₃.other .r10 (by decide), v₂.other .r10 (by decide),
        v₁.other .r10 (by decide)]
      exact ptr_step pu
    · rw [v₆.other .r9 (by decide), v₅.other .r9 (by decide), m₄.gpr, v₃.other .r9 (by decide),
        v₂.other .r9 (by decide), v₁.other .r9 (by decide)]
      exact p9u
  · rw [rsa_bytesAt, ← toBytes_encodeBE]
    exact VG.Proof.Weierstrass.bytesAt_eq_toBytes_len32 _ _ _ _ accepted (N := len / 4) (by omega_arith)
      (fun j hj hj4 => Vu j hj) fun k _ hk1 hk2 => absurd hk2 (by omega_arith)
  · rw [show len - 4 * (len / 4) = 0 by omega_arith, show 4 * (len / 4) = len by omega_arith] at Ou; exact Ou

end VG.Proof.Dsa.Arm

end

end

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
    obtain h1 := hx (0, 64) (by simp [arithRanges])
    obtain h2 := hx (256, 4704) (by simp [arithRanges])
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
  obtain P := pointerValue_keep h12 O hO R.ok
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
    obtain w₁ := hs.of_upd u₁ (by decide)
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
  obtain wu := hs.of_rest Ru (by decide)
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
  obtain Ru : Rest [.r3, .r4, .r11] s u := (((v₁.rest (by decide)).trans (v₂.rest (by decide))).trans
    (v₃.rest (by decide))).trans (v₄.rest (by decide))
  obtain wu := hs.of_rest Ru (by decide)
  obtain r11 : u.gpr .r11 = s.gpr .r12 + BitVec.ofNat 32 output := by
    rw [v₄.other .r11 (by decide), v₃.other .r11 (by decide), v₂.other .r11 (by decide), v₁.gpr]
  obtain pa : State.addr (u.gpr .r11) = off base output := by
    rw [r11]
    have := wu.ea (r := .r12) (K := 0) (d := output) (BitVec.add_zero _).symm (by omega_using [h4, ho])
    rwa [Nat.zero_add, Ru.gpr .r12 (by decide)] at this
  obtain pn : (u.gpr .r11).toNat = base.toNat + output := by
    rw [r11, BitVec.toNat_add, BitVec.toNat_ofNat, hs.wb_toNat, Nat.mod_eq_of_lt (by omega_using [h16o] : output < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega_using [h4, ho, nw])]
  obtain r3 : u.gpr .r3 = if true then BitVec.allOnes 32 else 0 := by
    rw [v₄.gpr, v₃.gpr, dpVal, v₂.gpr]; decide
  obtain mu : u.mem = s.mem := by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  obtain r9 : resS n + len ≤ output := by simp only [resS]; omega_using [hn, hsep]
  obtain hd : Region.Disjoint ⟨off base (resS n), len⟩ ⟨off base output, len⟩ :=
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

variable {umaal : Bool}

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
  obtain H := decodeBE_lt (Spec.Rsa.bytesAt s.mem (State.addr (pointerValue base s p)) len)
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
  obtain s0 := slot_lt (i := 0) n48 (by decide)
  obtain cb := contextBytes_le n48
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
    WP isa (Core.power umaal len expLen modulus a b output) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base output) len =
        Spec.Dsa.encodeBE len (operand base s a len ^ operand base s b expLen % m) ∧
      Stage base s t output len := by
  obtain ⟨n0, n48, hl, hl'⟩ := w.bounds
  obtain s0 := slot_lt (i := 0) n48 (by decide)
  obtain s8 := slot_lt (i := 8) n48 (by decide)
  obtain s9 := slot_lt (i := 9) n48 (by decide)
  obtain s11 := slot_lt (i := 11) n48 (by decide)
  have nw := hs.nowrap
  obtain cb := contextBytes_le n48
  obtain mlt : m < 256 ^ len := hm ▸ operand_lt base s _ len
  unfold Core.power
  dsimp only
  rw [← w.n_eq]
  refine WP.seq (WP.mono (load_ok (n := n) (dst := modS n) hs (by omega_arith) Rq (by simp only [modS]; omega_arith)
    (by simp only [modS]; omega_arith) (by omega_arith) w.four hl w.word (by simp only [modS]; omega_arith))
    fun u ⟨wu, Vu, Ru, Ou⟩ => ?_)
  obtain Ou' := Outs.of_slot (i := 0) Ou (by decide) n48
  obtain Rau := Ra.keep_rest Ru (O := Ou') (hO := arith_hdr)
  obtain Rbu := Rb.keep_rest Ru (O := Ou') (hO := arith_hdr)
  refine WP.seq (WP.seq (WP.mono (load_ok (n := n) (dst := baseS n) wu (by omega_arith) Rau
    (by simp only [baseS]; omega_arith) (by simp only [baseS]; omega_arith) (by omega_arith) w.four hl w.word
    (by simp only [baseS]; omega_arith)) fun u₁ ⟨w₁, A₁, R₁, O₁⟩ => ?_))
  obtain Rb₁ := Rbu.keep_rest R₁ (O := Outs.of_slot (i := 8) O₁ (by decide) n48) (hO := arith_hdr)
  refine WP.mono (load_ok (n := n) (dst := expS n) w₁ (by omega_arith) Rb₁
    (by simp only [expS]; omega_arith) (by simp only [expS]; omega_arith) (by omega_arith) he4 (by omega_arith) hwe
    (by simp only [expS]; omega_arith)) fun u₂ ⟨w₂, B₂, R₂, O₂⟩ => ?_
  obtain K₂ : Outs base arithRanges s.mem u₂.mem :=
    (Ou'.trans (Outs.of_slot (i := 8) O₁ (by decide) n48)).trans (Outs.of_slot (i := 11) O₂ (by decide) n48)
  obtain R₂' : Rest coreClob s u₂ := ((Ru.mono (by decide)).trans (R₁.mono (by decide))).trans (R₂.mono (by decide))
  -- The values.
  obtain M₂ : val32 u₂.mem base (slot n 0) (2 * n) = m := by
    rw [O₂.val32 (by simp only [expS, slot, stride]; omega_arith) (by simp only [slot, stride]; omega_arith),
      O₁.val32 (by simp only [baseS, slot, stride]; omega_arith) (by simp only [slot, stride]; omega_arith)]
    exact Vu.trans hm
  obtain A₂ : val32 u₂.mem base (slot n 8) (2 * n) = operand base s a len := by
    rw [O₂.val32 (by simp only [expS, slot, stride]; omega_arith) (by simp only [slot, stride]; omega_arith)]
    exact A₁.trans (Ra.arith (Ru.gpr .r12 (by decide)) Ou')
  obtain B₂' : val32 u₂.mem base (slot n 11) (2 * n) = operand base s b expLen := by
    refine B₂.trans ?_
    rw [operand, pointerValue_keep (R₁.gpr .r12 (by decide)) (Outs.of_slot (i := 8) O₁ (by decide) n48) arith_hdr Rbu.ok,
      Rbu.bytes (Outs.of_slot (i := 8) O₁ (by decide) n48) (by decide)]
    exact Rb.arith (Ru.gpr .r12 (by decide)) Ou'
  obtain ek : (expLen + 3) / 4 ≤ 2 * n := by omega_arith
  obtain E₂ : val32 u₂.mem base (slot n 11) ((expLen + 3) / 4) = operand base s b expLen := by
    rw [val32_prefix_of_lt ek (by rw [B₂']; exact decoded_exponent_fits _ _ _), B₂']
  refine WP.seq (WP.mono (Pow.call_ok w₂ (by omega_arith) n0 n48 (by omega_arith) ek M₂ hm1 hodd)
    fun u₃ ⟨w₃, V₃, O₃, R₃⟩ => ?_)
  refine WP.mono (store_ok (output := output) w₃ w.n_eq.symm w.four w.word (by omega_arith) (by omega_arith) ho'
    h16o (by omega_arith)) fun t ⟨Vt, Rt, Ot⟩ => ⟨?_, R₂'.trans ((R₃.mono (by decide)).trans (Rt.mono (by decide))),
      ((Outs.arith_out K₂ _ _).trans (Outs.arith_out (Outs.arith O₃ (scratch_arith n48)) _ _)).trans
        (Outs.out Ot)⟩
  obtain lt₃ : val32 u₃.mem base (slot n 9) (2 * n) < m := by rw [V₃]; exact Nat.mod_lt _ (by omega_arith)
  rw [Vt, result_bytes w.word hl mlt lt₃, V₃, A₂, E₂]

theorem productMod_ok {s : State} {base : Addr} {size len n m output : Nat} {a b : Pointer} {modulus : Field}
    (hs : Ws s base size) (hz : 4960 ≤ size) (w : Width len n)
    (Rq : Ready s base (.input modulus) len) (Ra : Ready s base a len) (Rb : Ready s base b len)
    (hm : operand base s (.input modulus) len = m) (hm1 : 1 < m) (hodd : m % 2 = 1)
    (ho : 4960 ≤ output) (ho' : output + len ≤ size) (h16o : output < 2 ^ 16) :
    WP isa (Core.productMod umaal len modulus a b output) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base output) len =
        Spec.Dsa.encodeBE len (operand base s a len * operand base s b len % m) ∧
      Stage base s t output len := by
  obtain ⟨n0, n48, hl, hl'⟩ := w.bounds
  obtain s0 := slot_lt (i := 0) n48 (by decide)
  obtain s8 := slot_lt (i := 8) n48 (by decide)
  obtain s9 := slot_lt (i := 9) n48 (by decide)
  obtain s11 := slot_lt (i := 11) n48 (by decide)
  have nw := hs.nowrap
  obtain cb := contextBytes_le n48
  obtain mlt : m < 256 ^ len := hm ▸ operand_lt base s _ len
  unfold Core.productMod
  dsimp only
  rw [← w.n_eq]
  refine WP.seq (WP.mono (load_ok (n := n) (dst := modS n) hs (by omega_arith) Rq (by simp only [modS]; omega_arith)
    (by simp only [modS]; omega_arith) (by omega_arith) w.four hl w.word (by simp only [modS]; omega_arith))
    fun u ⟨wu, Vu, Ru, Ou⟩ => ?_)
  obtain Ou' := Outs.of_slot (i := 0) Ou (by decide) n48
  obtain Rau := Ra.keep_rest Ru (O := Ou') (hO := arith_hdr)
  obtain Rbu := Rb.keep_rest Ru (O := Ou') (hO := arith_hdr)
  refine WP.seq (WP.seq (WP.mono (load_ok (n := n) (dst := baseS n) wu (by omega_arith) Rau
    (by simp only [baseS]; omega_arith) (by simp only [baseS]; omega_arith) (by omega_arith) w.four hl w.word
    (by simp only [baseS]; omega_arith)) fun u₁ ⟨w₁, A₁, R₁, O₁⟩ => ?_))
  obtain Rb₁ := Rbu.keep_rest R₁ (O := Outs.of_slot (i := 8) O₁ (by decide) n48) (hO := arith_hdr)
  refine WP.mono (load_ok (n := n) (dst := expS n) w₁ (by omega_arith) Rb₁
    (by simp only [expS]; omega_arith) (by simp only [expS]; omega_arith) (by omega_arith) w.four hl w.word
    (by simp only [expS]; omega_arith)) fun u₂ ⟨w₂, B₂, R₂, O₂⟩ => ?_
  obtain K₂ : Outs base arithRanges s.mem u₂.mem :=
    (Ou'.trans (Outs.of_slot (i := 8) O₁ (by decide) n48)).trans (Outs.of_slot (i := 11) O₂ (by decide) n48)
  obtain R₂' : Rest coreClob s u₂ := ((Ru.mono (by decide)).trans (R₁.mono (by decide))).trans (R₂.mono (by decide))
  obtain M₂ : val32 u₂.mem base (slot n 0) (2 * n) = m := by
    rw [O₂.val32 (by simp only [expS, slot, stride]; omega_arith) (by simp only [slot, stride]; omega_arith),
      O₁.val32 (by simp only [baseS, slot, stride]; omega_arith) (by simp only [slot, stride]; omega_arith)]
    exact Vu.trans hm
  obtain A₂ : val32 u₂.mem base (slot n 8) (2 * n) = operand base s a len := by
    rw [O₂.val32 (by simp only [expS, slot, stride]; omega_arith) (by simp only [slot, stride]; omega_arith)]
    exact A₁.trans (Ra.arith (Ru.gpr .r12 (by decide)) Ou')
  obtain B₂' : val32 u₂.mem base (slot n 11) (2 * n) = operand base s b len := by
    refine B₂.trans ?_
    rw [operand, pointerValue_keep (R₁.gpr .r12 (by decide)) (Outs.of_slot (i := 8) O₁ (by decide) n48) arith_hdr Rbu.ok,
      Rbu.bytes (Outs.of_slot (i := 8) O₁ (by decide) n48) (by decide)]
    exact Rb.arith (Ru.gpr .r12 (by decide)) Ou'
  refine WP.seq (WP.mono (Pow.mulCall_ok w₂ (by omega_arith) n0 n48 M₂ hm1 hodd) fun u₃ ⟨w₃, V₃, O₃, R₃⟩ => ?_)
  refine WP.mono (store_ok (output := output) w₃ w.n_eq.symm w.four w.word (by omega_arith) (by omega_arith) ho'
    h16o (by omega_arith)) fun t ⟨Vt, Rt, Ot⟩ => ⟨?_, R₂'.trans ((R₃.mono (by decide)).trans (Rt.mono (by decide))),
      ((Outs.arith_out K₂ _ _).trans (Outs.arith_out (Outs.arith O₃ (scratch_arith n48)) _ _)).trans
        (Outs.out Ot)⟩
  obtain lt₃ : val32 u₃.mem base (slot n 9) (2 * n) < m := by rw [V₃]; exact Nat.mod_lt _ (by omega_arith)
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
  obtain s8 := slot_lt (i := 8) n48 (by decide)
  obtain s9 := slot_lt (i := 9) n48 (by decide)
  obtain s11 := slot_lt (i := 11) n48 (by decide)
  have nw := hs.nowrap
  obtain mlt : m < 256 ^ len := hm ▸ operand_lt base s _ len
  unfold Core.sum
  dsimp only
  rw [← w.n_eq]
  refine WP.seq (WP.mono (setup_ok hs hz w Rq hm hm1 hodd) fun u ⟨cu, Ou, Ru⟩ => ?_)
  obtain Rau := Ra.keep_rest Ru (O := Ou) (hO := arith_hdr)
  obtain Rbu := Rb.keep_rest Ru (O := Ou) (hO := arith_hdr)
  refine WP.seq (WP.seq (WP.mono (load_ok (n := n) (dst := baseS n) cu.ws (by omega_arith) Rau
    (by simp only [baseS]; omega_arith) (by simp only [baseS]; omega_arith) (by omega_arith) w.four hl w.word
    (by simp only [baseS]; omega_arith)) fun u₁ ⟨w₁, A₁, R₁, O₁⟩ => ?_))
  obtain c₁ := cu.of_slot w₁ O₁ (by decide)
  obtain Rb₁ := Rbu.keep_rest R₁ (O := Outs.of_slot (i := 8) O₁ (by decide) n48) (hO := arith_hdr)
  refine WP.mono (load_ok (n := n) (dst := expS n) c₁.ws (by omega_arith) Rb₁
    (by simp only [expS]; omega_arith) (by simp only [expS]; omega_arith) (by omega_arith) w.four hl w.word
    (by simp only [expS]; omega_arith)) fun u₂ ⟨w₂, B₂, R₂, O₂⟩ => ?_
  obtain c₂ := c₁.of_slot w₂ O₂ (by decide)
  obtain K₂ : Outs base arithRanges s.mem u₂.mem :=
    (Ou.trans (Outs.of_slot (i := 8) O₁ (by decide) n48)).trans (Outs.of_slot (i := 11) O₂ (by decide) n48)
  obtain R₂' : Rest coreClob s u₂ := (Ru.trans (R₁.mono (by decide))).trans (R₂.mono (by decide))
  obtain A₂ : val32 u₂.mem base (slot n 8) (2 * n) = operand base s a len := by
    rw [O₂.val32 (by simp only [expS, slot, stride]; omega_arith) (by simp only [slot, stride]; omega_arith)]
    exact A₁.trans (Ra.arith (Ru.gpr .r12 (by decide)) Ou)
  obtain B₂' : val32 u₂.mem base (slot n 11) (2 * n) = operand base s b len := by
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
  obtain lt₃ : val32 u₃.mem base (slot n 9) (2 * n) < m := by rw [V₃]; exact Nat.mod_lt _ (by omega_arith)
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
    obtain e : ∀ x : BitVec 32, BitVec.ofNat 32 x.toNat = x := fun x => by
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
  obtain s0 := slot_lt (i := 0) n48 (by decide)
  obtain s9 := slot_lt (i := 9) n48 (by decide)
  obtain cb := contextBytes_le n48
  have nw := hs.nowrap
  obtain mlt : m < 256 ^ len := hm ▸ operand_lt base s _ len
  unfold Core.reduce
  dsimp only
  rw [← w.n_eq]
  refine WP.seq (WP.mono (load_ok (n := n) (dst := modS n) hs (by omega_arith) Rq (by simp only [modS]; omega_arith)
    (by simp only [modS]; omega_arith) (by omega_arith) w.four hl w.word (by simp only [modS]; omega_arith))
    fun u ⟨wu, Vu, Ru, Ou⟩ => ?_)
  obtain Ou' := Outs.of_slot (i := 0) Ou (by decide) n48
  obtain Riu := Ri.keep_rest Ru (O := Ou') (hO := arith_hdr)
  obtain Cu := countValue_keep Ou' arith_hdr hc
  rw [← Cu] at Riu
  refine WP.seq (VG.Proof.X25519.Arm.WP.append (pointer_ok wu (by omega_arith) Riu.ok) fun v ⟨Pv, Rv, Mv⟩ =>
    WP.mono (countEnd_ok (wu.of_rest Rv (by decide)) (by omega_arith) hc) fun x ⟨Lx, Rx, Mx⟩ => ?_)
  obtain Rux : Rest [.r4, .r11, .lr] u x := (Rv.mono (by decide)).trans (Rx.mono (by decide))
  obtain wx := wu.of_rest Rux (by decide)
  obtain Cv : countValue base v count = countValue base u count :=
    countValue_keep (rs := []) (fun x _ => by rw [Mv]) (by simp) hc
  obtain r11 : x.gpr .r11 = pointerValue base u input := by rw [Rx.gpr .r11 (by decide), Pv]
  rw [Cv, Pv] at Lx
  obtain cl : countValue base s count < 2 ^ 32 := by
    cases count with
    | imm len => exact Nat.lt_trans hc (by decide)
    | field f => exact BitVec.isLt _
  obtain Vx : val32 x.mem base (slot n 0) (2 * n) = m := by rw [Mx, Mv]; exact Vu.trans hm
  obtain hrx : InRegions (x.rd ++ x.wr) (State.addr (pointerValue base u input)) (countValue base u count) := by
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
  obtain lt : val32 y.mem base (slot n 9) (2 * n) < m := by rw [Vy]; exact Nat.mod_lt _ (by omega_arith)
  rw [Vt, result_bytes w.word hl mlt lt, Vy, Mx, Mv, Cu]
  exact congrArg (fun v => Spec.Dsa.encodeBE len (v % m)) (Ri.arith (Ru.gpr .r12 (by decide)) Ou')

end VG.Proof.Dsa.Arm

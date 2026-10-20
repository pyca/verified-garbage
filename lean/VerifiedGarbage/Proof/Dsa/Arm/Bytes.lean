module

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
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

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
  have h' := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq
  have := x.isLt; have := e.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h' ⊢
  omega

/-- `r8` a word lower. -/
theorem r8_down {x e : BitVec 32} {j : Nat} (h : x + BitVec.ofNat 32 (4 * j) = e) :
    x - BitVec.ofNat 32 4 + BitVec.ofNat 32 (4 * (j + 1)) = e := by
  rw [← h]
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

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
    refine VG.Proof.X25519.Arm.WP.append (zeroPadInline_ok hs h10 hK hK4 k (by omega)) fun s₁ ⟨w₁, e₁, R₁, O₁⟩ => ?_
    refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => ?_
    have w₂ := w₁.of_upd u₂ (by decide)
    refine wp_str (by omega) (w₂.ea (K := o) (d := 4 * k) (by
      rw [u₂.other .r10 (by decide), u₂.other .r12 (by decide), R₁.gpr .r10 (by decide), R₁.gpr .r12 (by decide)]
      exact h10) (by omega)) (w₂.write (d := o + 4 * k) (n := 4) (by omega)) fun s₃ m₃ => WP.block_nil ?_
    have O₂ : Outside base (o + 4 * k) 4 s₁.mem s₃.mem := by
      rw [m₃.mem, u₂.mem]; exact writeW32_outside _ _ _ (by omega)
    refine ⟨w₂.of_mupd m₃, fun j hj => ?_, R₁.trans ((u₂.rest (by decide)).trans (m₃.rest _)),
      (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [O₂.w32 (by omega) (by omega), e₁ j h]
    · obtain rfl : j = k := by omega
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
  have R : Rest [.r4, .r9, .r10] s t :=
    ((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans (u₃.rest (by decide))
  have wt : Ws t base size := hs.of_rest R (by decide)
  have r4 : t.gpr .r4 = 0 := u₃.gpr
  have mt : t.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have p0 : t.gpr .r10 = s.gpr .r12 + BitVec.ofNat 32 o := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]; exact h10
  have p9 : t.gpr .r9 = s.gpr .r12 + BitVec.ofNat 32 (o + 4 * k) := by
    rw [u₃.other _ (by decide), u₂.gpr, VG.Proof.X25519.Arm.dpVal, u₁.gpr,
      u₁.other .r10 (by decide), h10, movw_ofNat h16, Offset.add_add]
  clear u₁ u₂ u₃
  refine ptrLoop_ok (A := s.gpr .r12 + BitVec.ofNat 32 o) (step := 4) (k := k)
    (fun j u => Ws u base size ∧ u.gpr .r4 = 0 ∧ Rest [.r4, .r9, .r10] s u ∧
      (∀ i < j, w32 u.mem base (o + 4 * i) = 0) ∧ Outside base o (4 * k) s.mem u.mem)
    (by decide) hk (by omega) (fun j u u' ⟨a, b, c, d, e⟩ f => ⟨a.of_fupd f, by rw [f.gpr]; exact b,
      c.trans (f.rest _), by rw [f.mem]; exact d, by rw [f.mem]; exact e⟩)
    ⟨wt, r4, R, fun i hi => absurd hi (Nat.not_lt_zero _), by rw [mt]; exact Outside.refl _ _ _ _⟩
    p0 (by rw [p9, Offset.add_add]) ?_ fun u ⟨a, _, c, d, e⟩ _ => ⟨a, d, e, c⟩
  intro j hj u ⟨wu, r4u, Ru, Vu, Ou⟩ pu p9u
  have e12 : u.gpr .r12 = s.gpr .r12 := Ru.gpr _ (by decide)
  refine wp_str (by decide) (wu.ea (K := o + 4 * j) (at_ptr pu e12) (by omega)) (wu.write (d := o + 4 * j + 0) (n := 4) (by omega))
    fun u₁ m₁ => wp_bump (by decide) fun u₂ v₂ => WP.block_nil ⟨⟨wu.of_mupd m₁ |>.of_upd v₂ (by decide), ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [v₂.other .r4 (by decide), m₁.gpr]; exact r4u
  · exact (Ru.trans (m₁.rest _)).trans (v₂.rest (by simp))
  · intro i hi
    rw [v₂.mem, m₁.mem]
    rcases Nat.lt_or_ge i j with h | h
    · rw [w32_write_lt (by omega) (by omega), Vu i h]
    · rw [show i = j by omega, Nat.add_zero, w32_write_self, r4u]; rfl
  · rw [v₂.mem, m₁.mem]; exact Ou.write32 (by omega) (by omega) (by omega) _
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
  · exact WP.mono (zeroPadLoop_ok hs h10 (by omega) hz (by omega))
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
  have hP : P.toNat = (s.gpr .r11).toNat := VG.Proof.X25519.Arm.addr_toNat _
  unfold loadComponent
  refine WP.seq (wp_movw fun s₀ u₀ => wp_dp (op2_reg _ _) fun s₁ u₁ =>
    wp_ptr (d := .r10) (by decide) (by omega) fun s₂ u₂ => wp_ptr (d := .r9) (by decide) (by omega) fun t u₃ =>
    WP.block_nil ?_)
  have R : Rest [.r4, .r8, .r9, .r10] s t := ((u₀.rest (by decide)).trans (u₁.rest (by decide))).trans
    ((u₂.rest (by decide)).trans (u₃.rest (by decide)))
  have mt : t.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem, u₀.mem]
  have r8 : t.gpr .r8 = s.gpr .r11 + BitVec.ofNat 32 (len - 4) := by
    simp only [u₃.get, u₂.get, u₁.get, u₀.get, reduceCtorEq, ↓reduceIte, VG.Proof.X25519.Arm.dpVal]
    rw [movw_ofNat (by omega)]
  have p10 : t.gpr .r10 = s.gpr .r12 + BitVec.ofNat 32 out := by
    simp only [u₃.get, u₂.get, u₁.get, u₀.get, reduceCtorEq, ↓reduceIte]
  have p9 : t.gpr .r9 = s.gpr .r12 + BitVec.ofNat 32 out + BitVec.ofNat 32 (4 * (len / 4)) := by
    simp only [u₃.get, u₂.get, u₁.get, u₀.get, reduceCtorEq, ↓reduceIte, Offset.add_add]
    rw [show 4 * (len / 4) = len by omega]
  clear u₀ u₁ u₂ u₃
  refine WP.seq (ptrLoop_ok (A := s.gpr .r12 + BitVec.ofNat 32 out) (step := 4) (k := len / 4)
    (fun j u => Ws u base size ∧ Rest [.r4, .r8, .r9, .r10] s u ∧
      u.gpr .r8 + BitVec.ofNat 32 (4 * j) = s.gpr .r11 + BitVec.ofNat 32 (len - 4) ∧
      Outside base out (4 * j) s.mem u.mem ∧ ∀ i < j, w32 u.mem base (out + 4 * i) = VG.Proof.Weierstrass.ldWord32 s.mem P len i)
    (by decide) (by omega) (by omega)
    (fun j u u' ⟨a, b, c, d, e⟩ F => ⟨a.of_fupd F, b.trans (F.rest _), by rw [F.gpr]; exact c,
      by rw [F.mem]; exact d, by rw [F.mem]; exact e⟩)
    ⟨hs.of_rest R (by decide), R, by rw [r8, Nat.mul_zero]; exact BitVec.add_zero _,
      by rw [mt]; exact Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
    p10 p9 ?_ fun u I pu => ?_)
  · intro j hj u ⟨wu, Ru, e8, Ou, Vu⟩ pu p9u
    have e12 : u.gpr .r12 = s.gpr .r12 := Ru.gpr _ (by decide)
    have r8u : u.gpr .r8 = s.gpr .r11 + BitVec.ofNat 32 (len - 4 * (j + 1)) := r8_at e8 (by omega)
    have ha : State.addr (u.gpr .r8 + BitVec.ofNat 32 0) = P + BitVec.ofNat 64 (len - 4 * (j + 1)) := by
      rw [BitVec.add_zero, r8u]; exact VG.Arm.addr_add (by omega)
    have hrd : InRegions (u.rd ++ u.wr) (P + BitVec.ofNat 64 (len - 4 * (j + 1))) 4 := by
      rw [Ru.rd, Ru.wr]; exact hr _ (by omega)
    have hkeep : u.mem.readW (P + BitVec.ofNat 64 (len - 4 * (j + 1))) 32 =
        s.mem.readW (P + BitVec.ofNat 64 (len - 4 * (j + 1))) 32 :=
      readW32_keep fun i hi => VG.Proof.Weierstrass.keep_of_disjoint (Ou.mono (Nat.le_refl _) (by omega)) hd
        (by omega) (by omega) (by omega)
    refine wp_ldr (by decide) ha hrd fun u₁ v₁ => wp_rev fun u₂ v₂ => ?_
    have w₂ := (wu.of_upd v₁ (by decide)).of_upd v₂ (by decide)
    refine wp_str (by decide) (w₂.ea (K := out + 4 * j) (d := 0) (at_ptr (by
      rw [v₂.other .r10 (by decide), v₁.other .r10 (by decide)]; exact pu)
      (by rw [v₂.other .r12 (by decide), v₁.other .r12 (by decide)]; exact e12)) (by omega))
      (w₂.write (d := out + 4 * j + 0) (n := 4) (by omega)) fun u₃ m₃ => ?_
    refine wp_dp (VG.Proof.X25519.Arm.op2_imm (encodable_lt (n := 4) (by decide))) fun u₄ v₄ =>
      wp_bump (by decide) fun u₅ v₅ => WP.block_nil ?_
    have O₂ : Outside base (out + 4 * j) 4 u.mem u₃.mem := by
      rw [m₃.mem, v₂.mem, v₁.mem, Nat.add_zero]; exact writeW32_outside _ _ _ (by omega)
    have m₅ : u₅.mem = u₃.mem := by rw [v₅.mem, v₄.mem]
    refine ⟨⟨(((w₂.of_mupd m₃).of_upd v₄ (by decide)).of_upd v₅ (by decide)),
      Ru.trans ((((v₁.rest (by decide)).trans (v₂.rest (by decide))).trans (m₃.rest _)).trans
        ((v₄.rest (by decide)).trans (v₅.rest (by decide)))), ?_, ?_, fun i hi => ?_⟩, ?_, ?_⟩
    · rw [v₅.other .r8 (by decide), v₄.gpr, m₃.gpr, v₂.other .r8 (by decide), v₁.other .r8 (by decide)]
      exact r8_down e8
    · rw [m₅]; exact (Ou.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))
    · rw [m₅]
      rcases Nat.lt_or_ge i j with h | h
      · rw [O₂.w32 (by omega) (by omega), Vu i h]
      · obtain rfl : i = j := by omega
        rw [m₃.mem, v₂.mem, v₁.mem, Nat.add_zero, w32_write_self, v₂.gpr, v₁.gpr, hkeep, VG.Proof.Weierstrass.ldWord32,
          ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    · rw [v₅.gpr, v₄.other .r10 (by decide), m₃.gpr, v₂.other .r10 (by decide), v₁.other .r10 (by decide)]
      exact ptr_step pu
    · rw [v₅.other .r9 (by decide), v₄.other .r9 (by decide), m₃.gpr, v₂.other .r9 (by decide),
        v₁.other .r9 (by decide)]
      exact p9u
  · obtain ⟨wu, Ru, _, Ou, Vu⟩ := I
    have e12 : u.gpr .r12 = s.gpr .r12 := Ru.gpr _ (by decide)
    refine WP.mono (zeroPad_ok wu (o := out + len) (k := 2 * n - len / 4)
      (by rw [pu, e12, Offset.add_add, show out + 4 * (len / 4) = out + len by omega]) (by omega) (by omega)) fun t ⟨wt, Z, R₂, O₂⟩ => ⟨wt, ?_, Ru.trans (R₂.mono (by decide)), ?_⟩
    · rw [decodeBE_ofBytes, rsa_bytesAt]
      refine VG.Proof.Weierstrass.val32_eq_ofBytes_len _ _ _ _ out (2 * n) len h4 (by omega) fun j hj => ?_
      rcases Nat.lt_or_ge j (len / 4) with h | h
      · rw [O₂.w32 (by omega) (by omega), Vu j h]
      · rw [show out + 4 * j = out + len + 4 * (j - len / 4) by omega, Z _ (by omega),
          VG.Proof.Weierstrass.ldWord32, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
          ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    · exact (Ou.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))

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
  have hP : P.toNat = (s.gpr .r11).toNat := VG.Proof.X25519.Arm.addr_toNat _
  let mask : BitVec 32 := if accepted then BitVec.allOnes 32 else 0
  unfold storeComponent
  refine WP.seq (wp_movw fun s₀ u₀ => wp_dp (op2_reg _ _) fun s₁ u₁ =>
    wp_ptr (d := .r10) (by decide) (by omega) fun s₂ u₂ => wp_ptr (d := .r9) (by decide) (by omega) fun t u₃ =>
    WP.block_nil ?_)
  have R : Rest [.r4, .r8, .r9, .r10] s t := ((u₀.rest (by decide)).trans (u₁.rest (by decide))).trans
    ((u₂.rest (by decide)).trans (u₃.rest (by decide)))
  have mt : t.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem, u₀.mem]
  have r8 : t.gpr .r8 = s.gpr .r11 + BitVec.ofNat 32 (len - 4) := by
    simp only [u₃.get, u₂.get, u₁.get, u₀.get, reduceCtorEq, ↓reduceIte, VG.Proof.X25519.Arm.dpVal]
    rw [movw_ofNat (by omega)]
  have p10 : t.gpr .r10 = s.gpr .r12 + BitVec.ofNat 32 input := by
    simp only [u₃.get, u₂.get, u₁.get, u₀.get, reduceCtorEq, ↓reduceIte]
  have p9 : t.gpr .r9 = s.gpr .r12 + BitVec.ofNat 32 input + BitVec.ofNat 32 (4 * (len / 4)) := by
    simp only [u₃.get, u₂.get, u₁.get, u₀.get, reduceCtorEq, ↓reduceIte, Offset.add_add]
    rw [show 4 * (len / 4) = len by omega]
  clear u₀ u₁ u₂ u₃
  have hPl : P.toNat + len ≤ 2 ^ 64 := by omega
  refine ptrLoop_ok (A := s.gpr .r12 + BitVec.ofNat 32 input) (step := 4) (k := len / 4)
    (fun j u => Ws u base size ∧ Rest [.r4, .r8, .r9, .r10] s u ∧
      u.gpr .r8 + BitVec.ofNat 32 (4 * j) = s.gpr .r11 + BitVec.ofNat 32 (len - 4) ∧
      Outside P (len - 4 * j) (4 * j) s.mem u.mem ∧
      ∀ i < j, u.mem.readW (P + BitVec.ofNat 64 (len - 4 * (i + 1))) 32 =
        byteRev32 (s.mem.readW (off base (input + 4 * i)) 32 &&& mask))
    (by decide) (by omega) (by omega)
    (fun j u u' ⟨a, b, c, d, e⟩ F => ⟨a.of_fupd F, b.trans (F.rest _), by rw [F.gpr]; exact c,
      by rw [F.mem]; exact d, by rw [F.mem]; exact e⟩)
    ⟨hs.of_rest R (by decide), R, by rw [r8, Nat.mul_zero]; exact BitVec.add_zero _,
      by rw [mt]; exact Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
    p10 p9 ?_ fun u ⟨wu, Ru, _, Ou, Vu⟩ _ => ⟨wu, ?_, Ru, ?_⟩
  · intro j hj u ⟨wu, Ru, e8, Ou, Vu⟩ pu p9u
    have e12 : u.gpr .r12 = s.gpr .r12 := Ru.gpr _ (by decide)
    have r8u : u.gpr .r8 = s.gpr .r11 + BitVec.ofNat 32 (len - 4 * (j + 1)) := r8_at e8 (by omega)
    have hword : u.mem.readW (off base (input + 4 * j + 0)) 32 = s.mem.readW (off base (input + 4 * j)) 32 := by
      rw [Nat.add_zero]
      show u.mem.readW (base + BitVec.ofNat 64 (input + 4 * j)) 32 = s.mem.readW (base + BitVec.ofNat 64 (input + 4 * j)) 32
      rw [← Offset.add_add]
      exact readW32_keep fun i hi => VG.Proof.Weierstrass.keep_of_disjoint' (Ou.mono (Nat.zero_le _) (by omega)) hd
        (by omega) (by omega) (by omega)
    refine wp_ldr (by decide) (wu.ea (K := input + 4 * j) (d := 0) (at_ptr pu e12) (by omega))
      (wu.read (d := input + 4 * j + 0) (n := 4) (by omega)) fun u₁ v₁ => ?_
    refine wp_dp (op2_reg _ _) fun u₂ v₂ => wp_rev fun u₃ v₃ => ?_
    have w₃ := ((wu.of_upd v₁ (by decide)).of_upd v₂ (by decide)).of_upd v₃ (by decide)
    have ha₃ : State.addr (u₃.gpr .r8 + BitVec.ofNat 32 0) = P + BitVec.ofNat 64 (len - 4 * (j + 1)) := by
      rw [BitVec.add_zero, v₃.other .r8 (by decide), v₂.other .r8 (by decide), v₁.other .r8 (by decide), r8u]
      exact VG.Arm.addr_add (by omega)
    have hw₃ : InRegions u₃.wr (P + BitVec.ofNat 64 (len - 4 * (j + 1))) 4 := by
      rw [v₃.wr, v₂.wr, v₁.wr, Ru.wr]; exact hw _ _ (by omega)
    refine wp_str (by decide) ha₃ hw₃ fun u₄ m₄ => ?_
    refine wp_dp (VG.Proof.X25519.Arm.op2_imm (encodable_lt (n := 4) (by decide))) fun u₅ v₅ =>
      wp_bump (by decide) fun u₆ v₆ => WP.block_nil ?_
    have v₃' : u₃.gpr .r4 = byteRev32 (s.mem.readW (off base (input + 4 * j)) 32 &&& mask) := by
      rw [v₃.gpr, v₂.gpr, VG.Proof.X25519.Arm.dpVal, v₁.gpr, v₁.other .r3 (by decide), Ru.gpr .r3 (by decide), hc,
        hword]
    have mem₃ : u₃.mem = u.mem := by rw [v₃.mem, v₂.mem, v₁.mem]
    have O₂ : Outside P (len - 4 * (j + 1)) 4 u.mem u₄.mem := by
      rw [m₄.mem, mem₃]; exact writeW32_outside _ _ _ (by omega)
    have m₆ : u₆.mem = u₄.mem := by rw [v₆.mem, v₅.mem]
    refine ⟨⟨(((w₃.of_mupd m₄).of_upd v₅ (by decide)).of_upd v₆ (by decide)),
      Ru.trans ((((v₁.rest (by decide)).trans (v₂.rest (by decide))).trans ((v₃.rest (by decide)).trans
        (m₄.rest _))).trans ((v₅.rest (by decide)).trans (v₆.rest (by decide)))), ?_, ?_, fun i hi => ?_⟩, ?_, ?_⟩
    · rw [v₆.other .r8 (by decide), v₅.gpr, m₄.gpr, v₃.other .r8 (by decide), v₂.other .r8 (by decide),
        v₁.other .r8 (by decide)]
      exact r8_down e8
    · rw [m₆]; exact (Ou.mono (by omega) (by omega)).trans (O₂.mono (by omega) (by omega))
    · rw [m₆]
      rcases Nat.lt_or_ge i j with h | h
      · rw [m₄.mem, mem₃, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide), Vu i h]
      · obtain rfl : i = j := by omega
        rw [m₄.mem, Mem.readW_writeW_self32, v₃']
    · rw [v₆.gpr, v₅.other .r10 (by decide), m₄.gpr, v₃.other .r10 (by decide), v₂.other .r10 (by decide),
        v₁.other .r10 (by decide)]
      exact ptr_step pu
    · rw [v₆.other .r9 (by decide), v₅.other .r9 (by decide), m₄.gpr, v₃.other .r9 (by decide),
        v₂.other .r9 (by decide), v₁.other .r9 (by decide)]
      exact p9u
  · rw [rsa_bytesAt, ← toBytes_encodeBE]
    exact VG.Proof.Weierstrass.bytesAt_eq_toBytes_len32 _ _ _ _ accepted (N := len / 4) (by omega)
      (fun j hj hj4 => Vu j hj) fun k _ hk1 hk2 => absurd hk2 (by omega)
  · rw [show len - 4 * (len / 4) = 0 by omega, show 4 * (len / 4) = len by omega] at Ou; exact Ou

end VG.Proof.Dsa.Arm

import VerifiedGarbage.Proof.Ed448.X86.VerifyField
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.X448.X86.ByteMem
import VerifiedGarbage.Proof.X448.X86.Iter

/-!
# Ed448 verification's equation on x86 (32-bit): the bits of `S` and `k`

`vbits_ok`: byte `t` at `BITS` is bit `t` of `S` (the signature's last 57
bytes) plus twice bit `t` of `k` (the challenge), for `t < 456`.
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Impl.Ed448.X86 VG.Proof.X448.X86
open VG.Impl.X448.X86 (BITS at_)
open VG.Spec.Ed448 (bytesAt decodeLE)

/-- Bits `t` of two numbers in one byte. -/
def pair2 (a b t : Nat) : Nat := ((a >>> t) &&& 1) + 2 * ((b >>> t) &&& 1)

theorem shiftReg_ok {s : State} {d src : Reg} {j : Nat} (hj : j < 8) :
    WP isa (.block (([.mov d (.reg src)] : List Instr) ++ if j = 0 then [] else [.shift .shr d j])) s
      fun t => t.gpr d = s.gpr src >>> j ∧ t.mem = s.mem ∧ Keeps [d] s t := by
  refine wp_mov rfl fun t ht => ?_
  by_cases hz : j = 0
  · subst j
    exact WP.block_nil ⟨ht.gpr, ht.mem, ht.rest (by simp)⟩
  · rw [ite_eq_right hz]
    refine wp_shift (by omega) fun u hu => WP.block_nil ⟨?_, hu.mem.trans ht.mem,
      (ht.rest (by simp)).trans (hu.rest (by simp))⟩
    rw [hu.gpr, ht.gpr]

theorem bit32 : ∀ b : BitVec 8, ∀ j < 8,
    (b.setWidth 32 >>> j) &&& (1 : BitVec 32) = BitVec.ofNat 32 ((b.toNat >>> j) &&& 1) := by
  decide +kernel

theorem pack2 (x y : Nat) :
    (BitVec.ofNat 32 x + BitVec.ofNat 32 y + BitVec.ofNat 32 y).setWidth 8 = BitVec.ofNat 8 (x + 2 * y) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem vbitJ_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 57)
    {a b : BitVec 8} (ha : s.gpr .eax = a.setWidth 32) (hb : s.gpr .ecx = b.setWidth 32) {j : Nat}
    (hj : j < 8) :
    WP isa (.block (vbitJ i j)) s fun t =>
      t.mem = s.mem.writeW (off base (BITS + (8 * i + j))) (BitVec.ofNat 8 (pair2 a.toNat b.toNat j)) ∧
        Keeps [.edx, .ebx] s t := by
  unfold vbitJ
  simp only [List.append_assoc]
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (shiftReg_ok (d := .edx) (src := .eax) hj) fun t1 ⟨e1, m1, k1⟩ => ?_
  refine wp_alu (Or.inr (Or.inr (Or.inl rfl))) rfl fun t2 v2 _ => ?_
  change WP isa (.block (([.mov .ebx (.reg .ecx)] : List Instr) ++ (if j = 0 then [] else [.shift .shr .ebx j]) ++
    [.alu .and .ebx (.imm 1), .alu .add .edx (.reg .ebx), .alu .add .edx (.reg .ebx),
      .store8 (Impl.X448.X86.sc (BITS + 8 * i + j)) .dl])) t2 _
  rw [WP.block_append_iff]
  refine WP.mono (shiftReg_ok (d := .ebx) (src := .ecx) hj) fun t3 ⟨e3, m3, k3⟩ => ?_
  refine wp_alu (Or.inr (Or.inr (Or.inl rfl))) rfl fun t4 v4 _ => ?_
  refine wp_alu (Or.inl rfl) rfl fun t5 v5 _ => ?_
  refine wp_alu (Or.inl rfl) rfl fun t6 v6 _ => ?_
  have k6 : Keeps [.edx, .ebx] s t6 :=
    (k1.mono (by simp)).trans ((v2.rest (by simp)).trans ((k3.mono (by simp)).trans
      ((v4.rest (by simp)).trans ((v5.rest (by simp)).trans (v6.rest (by simp))))))
  have s6 := hs.of_keeps k6 (by decide)
  refine wp_store8 (s6.ea (d := BITS + 8 * i + j) (by simp only [BITS]; omega))
    (s6.write (d := BITS + 8 * i + j) (n := 1) (by simp only [BITS]; omega)) fun t7 v7 =>
    WP.block_nil ⟨?_, k6.trans (v7.rest _)⟩
  have ex : t2.gpr .edx = BitVec.ofNat 32 ((a.toNat >>> j) &&& 1) := by
    rw [v2.gpr]; change t1.gpr .edx &&& 1 = _
    rw [e1, ha, bit32 a j hj]
  have ey : t4.gpr .ebx = BitVec.ofNat 32 ((b.toNat >>> j) &&& 1) := by
    rw [v4.gpr]; change t3.gpr .ebx &&& 1 = _
    rw [e3, v2.other _ (by decide), k1.1 _ (by decide), hb, bit32 b j hj]
  rw [v7.mem, v6.mem, v5.mem, v4.mem, m3, v2.mem, m1, Reg8.reg, v6.gpr]
  change s.mem.writeW _ ((t5.gpr .edx + t5.gpr .ebx).setWidth 8) = _
  rw [v5.gpr, v5.other _ (by decide)]
  change s.mem.writeW _ ((t4.gpr .edx + t4.gpr .ebx + t4.gpr .ebx).setWidth 8) = _
  rw [v4.other _ (by decide), (k3.1 _ (by decide) : t3.gpr .edx = t2.gpr .edx), ex, ey,
    pack2, Nat.add_assoc]
  rfl

theorem vbitsJ_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 57)
    {a b : BitVec 8} (ha : s.gpr .eax = a.setWidth 32) (hb : s.gpr .ecx = b.setWidth 32) :
    WP isa (.block ((List.range 8).flatMap (vbitJ i))) s fun t =>
      (∀ j < 8, t.mem (off base (BITS + (8 * i + j))) = BitVec.ofNat 8 (pair2 a.toNat b.toNat j)) ∧
      Outside base (BITS + 8 * i) 8 s.mem t.mem ∧ Keeps [.edx, .ebx] s t := by
  let inv := fun n (t : State) =>
    (∀ j < n, t.mem (off base (BITS + (8 * i + j))) = BitVec.ofNat 8 (pair2 a.toNat b.toNat j)) ∧
    Outside base (BITS + 8 * i) 8 s.mem t.mem ∧ Keeps [.edx, .ebx] s t
  have step : ∀ n t, n < 8 → inv n t → WP isa (.block (vbitJ i n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (vbitJ_ok (hs.of_keeps tk (by decide)) hi
      ((tk.1 _ (by decide)).trans ha) ((tk.1 _ (by decide)).trans hb) hn) fun u ⟨um, uk⟩ => ?_
    refine ⟨?_, tm.trans ?_, tk.trans uk⟩
    · intro j hj
      rw [um, writeW8_apply]
      have eq : off base (BITS + (8 * i + j)) = off base (BITS + (8 * i + n)) ↔ j = n := by
        rw [off_eq_iff base (by simp only [BITS]; omega) (by simp only [BITS]; omega)]
        omega
      by_cases he : j = n
      · rw [ite_eq_left (eq.mpr he), he]
      · rw [ite_eq_right (fun h => he (eq.mp h))]; exact tf j (by omega)
    · intro x hx
      rw [um]
      exact writeW8_outside _ _ _ (by simp only [BITS]; omega) (by omega)
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hj => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

/-- The bytes of `S` (at `esi + 57`) and `k` (at `ebp`) expanded into their
bits at `BITS`. -/
theorem vbytes_ok {s : State} {base sq kq : Addr} (hs : Scr s base)
    (hsq : (s.gpr .esi).setWidth 64 + BitVec.ofNat 64 57 = sq) (hfs : (s.gpr .esi).toNat + 114 ≤ 2 ^ 32)
    (hkq : (s.gpr .ebp).setWidth 64 = kq) (hfk : (s.gpr .ebp).toNat + 57 ≤ 2 ^ 32)
    (hsr : ∀ i < 57, InRegions (s.rd ++ s.wr) (sq + BitVec.ofNat 64 i) 1)
    (hkr : ∀ i < 57, InRegions (s.rd ++ s.wr) (kq + BitVec.ofNat 64 i) 1)
    (hsd : ∀ i < 57, 8192 ≤ ofs base (sq + BitVec.ofNat 64 i))
    (hkd : ∀ i < 57, 8192 ≤ ofs base (kq + BitVec.ofNat 64 i)) :
    WP isa (.block ((List.range 57).flatMap vbyte)) s fun t =>
      Keeps [.eax, .ecx, .edx, .ebx] s t ∧ Outside base BITS 456 s.mem t.mem ∧
      ∀ j < 456, t.mem (off base (BITS + j)) =
        BitVec.ofNat 8 (pair2 (decodeLE (bytesAt s.mem sq 57)) (decodeLE (bytesAt s.mem kq 57)) j) := by
  let inv := fun n (t : State) => Keeps [.eax, .ecx, .edx, .ebx] s t ∧ Outside base BITS (8 * n) s.mem t.mem ∧
    ∀ j < 8 * n, t.mem (off base (BITS + j)) =
      BitVec.ofNat 8 (pair2 (s.mem (sq + BitVec.ofNat 64 (j / 8))).toNat
        (s.mem (kq + BitVec.ofNat 64 (j / 8))).toNat (j % 8))
  have step : ∀ n t, n < 57 → inv n t → WP isa (.block (vbyte n)) t (inv (n + 1)) := by
    intro n t hn ⟨tk, tm, tb⟩
    have eas : t.ea (at_ .esi (57 + n)) = sq + BitVec.ofNat 64 n := by
      change addr (t.gpr .esi) (57 + n) = _
      rw [tk.1 _ (by decide), addr_eq (by omega), ← hsq, Offset.add_add]
    unfold vbyte
    refine wp_load8 eas (by rw [tk.2.1, tk.2.2]; exact hsr n hn) fun u hu => ?_
    have eak : u.ea (at_ .ebp n) = kq + BitVec.ofNat 64 n := by
      change addr (u.gpr .ebp) n = _
      rw [hu.other _ (by decide), tk.1 _ (by decide), addr_eq (by omega), hkq]
    refine wp_load8 eak (by rw [hu.rd, hu.wr, tk.2.1, tk.2.2]; exact hkr n hn) fun v hv => ?_
    have vs := ((hs.of_keeps tk (by decide)).of_upd hu (by decide)).of_upd hv (by decide)
    refine WP.mono (vbitsJ_ok vs hn (a := t.mem (sq + BitVec.ofNat 64 n))
      (b := u.mem (kq + BitVec.ofNat 64 n)) (by rw [hv.other _ (by decide), hu.gpr]) hv.gpr)
      fun w ⟨wb, wm, wk⟩ => ?_
    have bs : t.mem (sq + BitVec.ofNat 64 n) = s.mem (sq + BitVec.ofNat 64 n) :=
      tm _ (Or.inr (by have := hsd n hn; simp only [BITS]; omega))
    have bk : u.mem (kq + BitVec.ofNat 64 n) = s.mem (kq + BitVec.ofNat 64 n) := by
      rw [hu.mem]; exact tm _ (Or.inr (by have := hkd n hn; simp only [BITS]; omega))
    rw [bs, bk] at wb
    refine ⟨tk.trans ((hu.rest (by simp)).trans ((hv.rest (by simp)).trans (wk.mono (by simp)))), ?_, ?_⟩
    · rw [hv.mem, hu.mem] at wm
      exact (tm.mono (by omega) (by omega)).trans (wm.mono (by omega) (by omega))
    · intro j hj
      rcases Nat.lt_or_ge j (8 * n) with h | h
      · rw [wm _ (Or.inl (by rw [ofs_off' base (by simp only [BITS]; omega)]; omega)), hv.mem, hu.mem]
        exact tb j h
      · have e := wb (j - 8 * n) (by omega)
        rw [show 8 * n + (j - 8 * n) = j by omega] at e
        rw [e, show j / 8 = n by omega, show j % 8 = j - 8 * n by omega]
  refine WP.mono (wp_range_flatMap (M := isa) (N := 57) inv step 57 (by decide) s
    ⟨Keeps.refl _ _, Outside.refl _ _ _ _, fun _ hj => by omega⟩) fun t ⟨tk, tm, tb⟩ =>
    ⟨tk, tm, fun j hj => by
      rw [tb j hj]
      unfold pair2
      rw [Proof.Ed448.scalar_bit _ _ hj, Proof.Ed448.scalar_bit _ _ hj]⟩

/-- `vbits`: the pointers to the signature and the challenge (the arguments at
`[esp + 8]` and `[esp + 12]`) into `esi` and `ebp`, and byte `t` of `BITS`
bit `t` of `S` plus twice bit `t` of `k`, for `t < 456`. -/
theorem vbits_ok {s : State} {base : Addr} (hs : Scr s base) {a8 a12 : Addr}
    (ha8 : s.ea (at_ .esp 8) = a8) (hr8 : InRegions (s.rd ++ s.wr) a8 4)
    (ha12 : s.ea (at_ .esp 12) = a12) (hr12 : InRegions (s.rd ++ s.wr) a12 4)
    {sg ch : BitVec 32} (hsg : s.mem.readW a8 32 = sg) (hch : s.mem.readW a12 32 = ch)
    (hfs : sg.toNat + 114 ≤ 2 ^ 32) (hfk : ch.toNat + 57 ≤ 2 ^ 32)
    (hsr : ∀ i < 57, InRegions (s.rd ++ s.wr) (sg.setWidth 64 + BitVec.ofNat 64 57 + BitVec.ofNat 64 i) 1)
    (hkr : ∀ i < 57, InRegions (s.rd ++ s.wr) (ch.setWidth 64 + BitVec.ofNat 64 i) 1)
    (hsd : ∀ i < 57, 8192 ≤ ofs base (sg.setWidth 64 + BitVec.ofNat 64 57 + BitVec.ofNat 64 i))
    (hkd : ∀ i < 57, 8192 ≤ ofs base (ch.setWidth 64 + BitVec.ofNat 64 i)) :
    WP isa (.block vbits) s fun t =>
      t.gpr .esi = sg ∧ Keeps [.esi, .ebp, .eax, .ecx, .edx, .ebx] s t ∧ Outside base BITS 456 s.mem t.mem ∧
      ∀ j < 456, t.mem (off base (BITS + j)) =
        BitVec.ofNat 8 (pair2 (decodeLE (bytesAt s.mem (sg.setWidth 64 + BitVec.ofNat 64 57) 57))
          (decodeLE (bytesAt s.mem (ch.setWidth 64) 57)) j) := by
  unfold vbits
  refine wp_load ha8 hr8 fun u hu => ?_
  refine wp_load (a := a12) (by change addr (u.gpr .esp) 12 = _; rw [hu.other _ (by decide)]; exact ha12)
    (by rw [hu.rd, hu.wr]; exact hr12) fun v hv => ?_
  rw [hu.mem, hch] at hv
  rw [hsg] at hu
  have vs := (hs.of_upd hu (by decide)).of_upd hv (by decide)
  have rr : v.rd ++ v.wr = s.rd ++ s.wr := by rw [hv.rd, hv.wr, hu.rd, hu.wr]
  change WP isa (.block ((List.range 57).flatMap vbyte)) v _
  refine WP.mono (vbytes_ok vs (sq := sg.setWidth 64 + BitVec.ofNat 64 57) (kq := ch.setWidth 64)
    (by rw [hv.other _ (by decide), hu.gpr]) (by rw [hv.other _ (by decide), hu.gpr]; exact hfs)
    (by rw [hv.gpr]) (by rw [hv.gpr]; exact hfk) (by rw [rr]; exact hsr) (by rw [rr]; exact hkr) hsd hkd)
    fun t ⟨tk, tm, tb⟩ => ⟨?_, ?_, ?_, ?_⟩
  · rw [tk.1 _ (by decide), hv.other _ (by decide), hu.gpr]
  · exact (hu.rest (by simp)).trans ((hv.rest (by simp)).trans (tk.mono (by simp)))
  · rw [hv.mem, hu.mem] at tm; exact tm
  · rw [hv.mem, hu.mem] at tb; exact tb

end VG.Proof.Ed448.X86

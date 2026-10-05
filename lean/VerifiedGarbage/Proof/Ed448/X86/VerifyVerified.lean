import VerifiedGarbage.Proof.Ed448.Signing
import VerifiedGarbage.Proof.X448.X86.Verified
import VerifiedGarbage.Impl.Ed448.X86.VerifyEquation
import VerifiedGarbage.Proof.Ed448.X86.ScalarVerified
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ed448.X86.VerifyLit
import VerifiedGarbage.Proof.Ed448.X86.BaseVerified
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.X86.Inline

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.VerifyField`. -/
section

/-!
# Ed448 verification's equation on x86 (32-bit): field programs

A list of field operations on the slots (`FOp`, `Impl/Ed448/Formulas.lean`)
runs as X448's field arithmetic on x86 (`field_ok`): the slots become the
operations' evaluation (`evalOps`, whose values for the doubling, the
addition and the steps of decoding are in `Proof/Ed448/VerifyFormulas.lean`).
`VKeep` is what the checks and decoding may change: the field operations'
registers, the counter `esi`, and the working space from `BAD` to the slots'
end and from X448's `ACC`.
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Impl.Ed448 VG.Impl.Ed448.X86 VG.Proof.X448.X86
open VG.Proof.Ed448 (idx fopValid evalOp evalOps pt)
open VG.Impl.X448.X86 (slot X2 ACC sc)

/-! ## Reading the working space -/

theorem rd_sc {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d + 4 ≤ 8192) :
    VG.X86.readSrc s (.mem (VG.Impl.X448.X86.sc d)) = some (VG.Proof.X448.X86.word s.mem base d) := by
  simp only [VG.X86.readSrc, hs.ea (d := d) (by omega), State.load32, hs.read (d := d) (n := 4) hd, ite_true]

/-! ## Field programs -/

theorem slot_idx {n : Nat} (h : n < 22) : slot n = slot (idx n).val := by
  simp only [idx, Nat.mod_eq_of_lt h]

theorem fop_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (op : FOp)
    (hv : fopValid op) :
    WP isa (toOp op).code s fun t =>
      VG.Proof.X448.X86.Keep base s t ∧ BoundedEnv t.mem base ∧ VG.Proof.X448.X86.E t.mem base = evalOp op (VG.Proof.X448.X86.E s.mem base) := by
  cases op with
  | mul o a b =>
    obtain ⟨h1, h2, h3⟩ := hv
    simp only [toOp, Impl.X448.X86.Op.code, VG.Proof.Ed448.X86.slot_idx h1, VG.Proof.Ed448.X86.slot_idx h2, VG.Proof.Ed448.X86.slot_idx h3]
    exact mulE hs hb _ _ _
  | sqr o a =>
    obtain ⟨h1, h2⟩ := hv
    simp only [toOp, Impl.X448.X86.Op.code, VG.Proof.Ed448.X86.slot_idx h1, VG.Proof.Ed448.X86.slot_idx h2]
    exact mulE hs hb _ _ _
  | add o a b =>
    obtain ⟨h1, h2, h3⟩ := hv
    simp only [toOp, Impl.X448.X86.Op.code, VG.Proof.Ed448.X86.slot_idx h1, VG.Proof.Ed448.X86.slot_idx h2, VG.Proof.Ed448.X86.slot_idx h3]
    exact addE hs hb _ _ _
  | sub o a b =>
    obtain ⟨h1, h2, h3⟩ := hv
    simp only [toOp, Impl.X448.X86.Op.code, VG.Proof.Ed448.X86.slot_idx h1, VG.Proof.Ed448.X86.slot_idx h2, VG.Proof.Ed448.X86.slot_idx h3]
    exact subE hs hb _ _ _

theorem field_ok (l : List FOp) (hv : ∀ op ∈ l, fopValid op) {s : State} {base : Addr}
    (hs : Scr s base) (hb : BoundedEnv s.mem base) :
    WP isa (VG.Impl.Ed448.X86.field l) s fun t =>
      VG.Proof.X448.X86.Keep base s t ∧ BoundedEnv t.mem base ∧ VG.Proof.X448.X86.E t.mem base = evalOps l (VG.Proof.X448.X86.E s.mem base) := by
  induction l generalizing s with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, hb, rfl⟩
  | cons op l ih =>
    change WP isa (.seq (toOp op).code (VG.Impl.Ed448.X86.field l)) s _
    rw [WP.seq_iff]
    refine WP.mono (VG.Proof.Ed448.X86.fop_ok hs hb op (hv op List.mem_cons_self)) fun t ⟨tk, tb, te⟩ => ?_
    refine WP.mono (ih (fun o h => hv o (List.mem_cons_of_mem _ h)) (tk.scr hs) tb)
      fun u ⟨uk, ub, ue⟩ => ⟨tk.trans uk, ub, by rw [ue, te]; rfl⟩

/-- A field program, then more code. -/
theorem field_seq (l : List FOp) (hv : ∀ op ∈ l, fopValid op) {s : State} {base : Addr}
    (hs : Scr s base) (hb : BoundedEnv s.mem base) {c : Prog isa} {Q : State → Prop}
    (k : ∀ t, VG.Proof.X448.X86.Keep base s t → BoundedEnv t.mem base → VG.Proof.X448.X86.E t.mem base = evalOps l (VG.Proof.X448.X86.E s.mem base) →
      WP isa c t Q) :
    WP isa (.seq (VG.Impl.Ed448.X86.field l) c) s Q :=
  WP.seq (WP.mono (VG.Proof.Ed448.X86.field_ok l hv hs hb) fun t ⟨kt, bt, et⟩ => k t kt bt et)

/-! ## The frame -/

/-- What the checks and decoding may change. -/
structure VKeep (base : Addr) (s t : State) : Prop where
  regs : Keeps (.esi :: workRegs) s t
  mem : Outside2 base 16 2864 ACC 512 s.mem t.mem

theorem VKeep.refl (base : Addr) (s : State) : VG.Proof.Ed448.X86.VKeep base s s :=
  ⟨Keeps.refl _ _, Outside2.refl _ _ _ _ _ _⟩

theorem VKeep.trans {base : Addr} {s t u : State} (h : VG.Proof.Ed448.X86.VKeep base s t) (h' : VG.Proof.Ed448.X86.VKeep base t u) :
    VG.Proof.Ed448.X86.VKeep base s u := ⟨h.regs.trans h'.regs, h.mem.trans h'.mem⟩

theorem VKeep.scr {base : Addr} {s t : State} (h : VG.Proof.Ed448.X86.VKeep base s t) (hs : Scr s base) : Scr t base :=
  hs.of_keeps h.regs (by decide)

theorem Outside2.widen {base : Addr} {m m' : Mem} (h : Outside2 base 64 2816 ACC 512 m m') :
    Outside2 base 16 2864 ACC 512 m m' :=
  fun p h1 h2 => h p (by rcases h1 with h1 | h1 <;> [exact Or.inl (by omega); exact Or.inr (by omega)]) h2

theorem IKeep.toV {base : Addr} {s t : State} (h : IKeep base s t) : VG.Proof.Ed448.X86.VKeep base s t :=
  ⟨h.regs, Outside2.widen h.mem⟩

theorem Keep.toV {base : Addr} {s t : State} (h : VG.Proof.X448.X86.Keep base s t) : VG.Proof.Ed448.X86.VKeep base s t := IKeep.toV h.ikeep

theorem slot_range (i : Index) : 64 ≤ slot i.val ∧ slot i.val + 112 ≤ 2880 := by
  have := i.isLt
  simp only [slot]
  omega

theorem outV {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') (h1 : 16 ≤ o)
    (h2 : o + n ≤ 2880) : Outside2 base 16 2864 ACC 512 m m' := fun p hp _ => h p (by omega)

theorem fmV {base : Addr} {o : Nat} {m m' : Mem} (h : FieldMem base o m m') (h1 : 16 ≤ o)
    (h2 : o + 112 ≤ 2880) : Outside2 base 16 2864 ACC 512 m m' := fun p hp hq => h p (by omega) hq

/-- The point in slots `i`, `j`, `k`, from equal slots. -/
theorem pt_congr' {e e' : Env} {a b c : Index} (ha : e' a = e a) (hb : e' b = e b) (hc : e' c = e c) :
    pt e' a b c = pt e a b c := by
  simp only [pt, ha, hb, hc]

end VG.Proof.Ed448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.VerifyBits`. -/
section

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
  refine VG.Proof.X448.X86.wp_mov rfl fun t ht => ?_
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
      t.mem = s.mem.writeW (off base (VG.Impl.X448.X86.BITS + (8 * i + j))) (BitVec.ofNat 8 (VG.Proof.Ed448.X86.pair2 a.toNat b.toNat j)) ∧
        Keeps [.edx, .ebx] s t := by
  unfold vbitJ
  simp only [List.append_assoc]
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86.shiftReg_ok (d := .edx) (src := .eax) hj) fun t1 ⟨e1, m1, k1⟩ => ?_
  refine wp_alu (Or.inr (Or.inr (Or.inl rfl))) rfl fun t2 v2 _ => ?_
  change WP isa (.block (([.mov .ebx (.reg .ecx)] : List Instr) ++ (if j = 0 then [] else [.shift .shr .ebx j]) ++
    [.alu .and .ebx (.imm 1), .alu .add .edx (.reg .ebx), .alu .add .edx (.reg .ebx),
      .store8 (Impl.X448.X86.sc (VG.Impl.X448.X86.BITS + 8 * i + j)) .dl])) t2 _
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86.shiftReg_ok (d := .ebx) (src := .ecx) hj) fun t3 ⟨e3, m3, k3⟩ => ?_
  refine wp_alu (Or.inr (Or.inr (Or.inl rfl))) rfl fun t4 v4 _ => ?_
  refine wp_alu (Or.inl rfl) rfl fun t5 v5 _ => ?_
  refine wp_alu (Or.inl rfl) rfl fun t6 v6 _ => ?_
  have k6 : Keeps [.edx, .ebx] s t6 :=
    (k1.mono (by simp)).trans ((v2.rest (by simp)).trans ((k3.mono (by simp)).trans
      ((v4.rest (by simp)).trans ((v5.rest (by simp)).trans (v6.rest (by simp))))))
  have s6 := hs.of_keeps k6 (by decide)
  refine VG.Proof.X448.X86.wp_store8 (s6.ea (d := VG.Impl.X448.X86.BITS + 8 * i + j) (by simp only [VG.Impl.X448.X86.BITS]; omega))
    (s6.write (d := VG.Impl.X448.X86.BITS + 8 * i + j) (n := 1) (by simp only [VG.Impl.X448.X86.BITS]; omega)) fun t7 v7 =>
    WP.block_nil ⟨?_, k6.trans (v7.rest _)⟩
  have ex : t2.gpr .edx = BitVec.ofNat 32 ((a.toNat >>> j) &&& 1) := by
    rw [v2.gpr]; change t1.gpr .edx &&& 1 = _
    rw [e1, ha, VG.Proof.Ed448.X86.bit32 a j hj]
  have ey : t4.gpr .ebx = BitVec.ofNat 32 ((b.toNat >>> j) &&& 1) := by
    rw [v4.gpr]; change t3.gpr .ebx &&& 1 = _
    rw [e3, v2.other _ (by decide), k1.1 _ (by decide), hb, VG.Proof.Ed448.X86.bit32 b j hj]
  rw [v7.mem, v6.mem, v5.mem, v4.mem, m3, v2.mem, m1, Reg8.reg, v6.gpr]
  change s.mem.writeW _ ((t5.gpr .edx + t5.gpr .ebx).setWidth 8) = _
  rw [v5.gpr, v5.other _ (by decide)]
  change s.mem.writeW _ ((t4.gpr .edx + t4.gpr .ebx + t4.gpr .ebx).setWidth 8) = _
  rw [v4.other _ (by decide), (k3.1 _ (by decide) : t3.gpr .edx = t2.gpr .edx), ex, ey,
    VG.Proof.Ed448.X86.pack2, Nat.add_assoc]
  rfl

theorem vbitsJ_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 57)
    {a b : BitVec 8} (ha : s.gpr .eax = a.setWidth 32) (hb : s.gpr .ecx = b.setWidth 32) :
    WP isa (.block ((List.range 8).flatMap (vbitJ i))) s fun t =>
      (∀ j < 8, t.mem (off base (VG.Impl.X448.X86.BITS + (8 * i + j))) = BitVec.ofNat 8 (VG.Proof.Ed448.X86.pair2 a.toNat b.toNat j)) ∧
      Outside base (VG.Impl.X448.X86.BITS + 8 * i) 8 s.mem t.mem ∧ Keeps [.edx, .ebx] s t := by
  let inv := fun n (t : State) =>
    (∀ j < n, t.mem (off base (VG.Impl.X448.X86.BITS + (8 * i + j))) = BitVec.ofNat 8 (VG.Proof.Ed448.X86.pair2 a.toNat b.toNat j)) ∧
    Outside base (VG.Impl.X448.X86.BITS + 8 * i) 8 s.mem t.mem ∧ Keeps [.edx, .ebx] s t
  have step : ∀ n t, n < 8 → inv n t → WP isa (.block (vbitJ i n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (VG.Proof.Ed448.X86.vbitJ_ok (hs.of_keeps tk (by decide)) hi
      ((tk.1 _ (by decide)).trans ha) ((tk.1 _ (by decide)).trans hb) hn) fun u ⟨um, uk⟩ => ?_
    refine ⟨?_, tm.trans ?_, tk.trans uk⟩
    · intro j hj
      rw [um, writeW8_apply]
      have eq : off base (VG.Impl.X448.X86.BITS + (8 * i + j)) = off base (VG.Impl.X448.X86.BITS + (8 * i + n)) ↔ j = n := by
        rw [off_eq_iff base (by simp only [VG.Impl.X448.X86.BITS]; omega) (by simp only [VG.Impl.X448.X86.BITS]; omega)]
        omega
      by_cases he : j = n
      · rw [ite_eq_left (eq.mpr he), he]
      · rw [ite_eq_right (fun h => he (eq.mp h))]; exact tf j (by omega)
    · intro x hx
      rw [um]
      exact writeW8_outside _ _ _ (by simp only [VG.Impl.X448.X86.BITS]; omega) (by omega)
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
      Keeps [.eax, .ecx, .edx, .ebx] s t ∧ Outside base VG.Impl.X448.X86.BITS 456 s.mem t.mem ∧
      ∀ j < 456, t.mem (off base (VG.Impl.X448.X86.BITS + j)) =
        BitVec.ofNat 8 (VG.Proof.Ed448.X86.pair2 (decodeLE (bytesAt s.mem sq 57)) (decodeLE (bytesAt s.mem kq 57)) j) := by
  let inv := fun n (t : State) => Keeps [.eax, .ecx, .edx, .ebx] s t ∧ Outside base VG.Impl.X448.X86.BITS (8 * n) s.mem t.mem ∧
    ∀ j < 8 * n, t.mem (off base (VG.Impl.X448.X86.BITS + j)) =
      BitVec.ofNat 8 (VG.Proof.Ed448.X86.pair2 (s.mem (sq + BitVec.ofNat 64 (j / 8))).toNat
        (s.mem (kq + BitVec.ofNat 64 (j / 8))).toNat (j % 8))
  have step : ∀ n t, n < 57 → inv n t → WP isa (.block (vbyte n)) t (inv (n + 1)) := by
    intro n t hn ⟨tk, tm, tb⟩
    have eas : t.ea (VG.Impl.X448.X86.at_ .esi (57 + n)) = sq + BitVec.ofNat 64 n := by
      change VG.X86.addr (t.gpr .esi) (57 + n) = _
      rw [tk.1 _ (by decide), addr_eq (by omega), ← hsq, Offset.add_add]
    unfold vbyte
    refine wp_load8 eas (by rw [tk.2.1, tk.2.2]; exact hsr n hn) fun u hu => ?_
    have eak : u.ea (VG.Impl.X448.X86.at_ .ebp n) = kq + BitVec.ofNat 64 n := by
      change VG.X86.addr (u.gpr .ebp) n = _
      rw [hu.other _ (by decide), tk.1 _ (by decide), addr_eq (by omega), hkq]
    refine wp_load8 eak (by rw [hu.rd, hu.wr, tk.2.1, tk.2.2]; exact hkr n hn) fun v hv => ?_
    have vs := ((hs.of_keeps tk (by decide)).of_upd hu (by decide)).of_upd hv (by decide)
    refine WP.mono (VG.Proof.Ed448.X86.vbitsJ_ok vs hn (a := t.mem (sq + BitVec.ofNat 64 n))
      (b := u.mem (kq + BitVec.ofNat 64 n)) (by rw [hv.other _ (by decide), hu.gpr]) hv.gpr)
      fun w ⟨wb, wm, wk⟩ => ?_
    have bs : t.mem (sq + BitVec.ofNat 64 n) = s.mem (sq + BitVec.ofNat 64 n) :=
      tm _ (Or.inr (by have := hsd n hn; simp only [VG.Impl.X448.X86.BITS]; omega))
    have bk : u.mem (kq + BitVec.ofNat 64 n) = s.mem (kq + BitVec.ofNat 64 n) := by
      rw [hu.mem]; exact tm _ (Or.inr (by have := hkd n hn; simp only [VG.Impl.X448.X86.BITS]; omega))
    rw [bs, bk] at wb
    refine ⟨tk.trans ((hu.rest (by simp)).trans ((hv.rest (by simp)).trans (wk.mono (by simp)))), ?_, ?_⟩
    · rw [hv.mem, hu.mem] at wm
      exact (tm.mono (by omega) (by omega)).trans (wm.mono (by omega) (by omega))
    · intro j hj
      rcases Nat.lt_or_ge j (8 * n) with h | h
      · rw [wm _ (Or.inl (by rw [ofs_off' base (by simp only [VG.Impl.X448.X86.BITS]; omega)]; omega)), hv.mem, hu.mem]
        exact tb j h
      · have e := wb (j - 8 * n) (by omega)
        rw [show 8 * n + (j - 8 * n) = j by omega] at e
        rw [e, show j / 8 = n by omega, show j % 8 = j - 8 * n by omega]
  refine WP.mono (wp_range_flatMap (M := isa) (N := 57) inv step 57 (by decide) s
    ⟨Keeps.refl _ _, Outside.refl _ _ _ _, fun _ hj => by omega⟩) fun t ⟨tk, tm, tb⟩ =>
    ⟨tk, tm, fun j hj => by
      rw [tb j hj]
      unfold VG.Proof.Ed448.X86.pair2
      rw [Proof.Ed448.scalar_bit _ _ hj, Proof.Ed448.scalar_bit _ _ hj]⟩

/-- `vbits`: the pointers to the signature and the challenge (the arguments at
`[esp + 8]` and `[esp + 12]`) into `esi` and `ebp`, and byte `t` of `BITS`
bit `t` of `S` plus twice bit `t` of `k`, for `t < 456`. -/
theorem vbits_ok {s : State} {base : Addr} (hs : Scr s base) {a8 a12 : Addr}
    (ha8 : s.ea (VG.Impl.X448.X86.at_ .esp 8) = a8) (hr8 : InRegions (s.rd ++ s.wr) a8 4)
    (ha12 : s.ea (VG.Impl.X448.X86.at_ .esp 12) = a12) (hr12 : InRegions (s.rd ++ s.wr) a12 4)
    {sg ch : BitVec 32} (hsg : s.mem.readW a8 32 = sg) (hch : s.mem.readW a12 32 = ch)
    (hfs : sg.toNat + 114 ≤ 2 ^ 32) (hfk : ch.toNat + 57 ≤ 2 ^ 32)
    (hsr : ∀ i < 57, InRegions (s.rd ++ s.wr) (sg.setWidth 64 + BitVec.ofNat 64 57 + BitVec.ofNat 64 i) 1)
    (hkr : ∀ i < 57, InRegions (s.rd ++ s.wr) (ch.setWidth 64 + BitVec.ofNat 64 i) 1)
    (hsd : ∀ i < 57, 8192 ≤ ofs base (sg.setWidth 64 + BitVec.ofNat 64 57 + BitVec.ofNat 64 i))
    (hkd : ∀ i < 57, 8192 ≤ ofs base (ch.setWidth 64 + BitVec.ofNat 64 i)) :
    WP isa (.block vbits) s fun t =>
      t.gpr .esi = sg ∧ Keeps [.esi, .ebp, .eax, .ecx, .edx, .ebx] s t ∧ Outside base VG.Impl.X448.X86.BITS 456 s.mem t.mem ∧
      ∀ j < 456, t.mem (off base (VG.Impl.X448.X86.BITS + j)) =
        BitVec.ofNat 8 (VG.Proof.Ed448.X86.pair2 (decodeLE (bytesAt s.mem (sg.setWidth 64 + BitVec.ofNat 64 57) 57))
          (decodeLE (bytesAt s.mem (ch.setWidth 64) 57)) j) := by
  unfold vbits
  refine wp_load ha8 hr8 fun u hu => ?_
  refine wp_load (a := a12) (by change VG.X86.addr (u.gpr .esp) 12 = _; rw [hu.other _ (by decide)]; exact ha12)
    (by rw [hu.rd, hu.wr]; exact hr12) fun v hv => ?_
  rw [hu.mem, hch] at hv
  rw [hsg] at hu
  have vs := (hs.of_upd hu (by decide)).of_upd hv (by decide)
  have rr : v.rd ++ v.wr = s.rd ++ s.wr := by rw [hv.rd, hv.wr, hu.rd, hu.wr]
  change WP isa (.block ((List.range 57).flatMap vbyte)) v _
  refine WP.mono (VG.Proof.Ed448.X86.vbytes_ok vs (sq := sg.setWidth 64 + BitVec.ofNat 64 57) (kq := ch.setWidth 64)
    (by rw [hv.other _ (by decide), hu.gpr]) (by rw [hv.other _ (by decide), hu.gpr]; exact hfs)
    (by rw [hv.gpr]) (by rw [hv.gpr]; exact hfk) (by rw [rr]; exact hsr) (by rw [rr]; exact hkr) hsd hkd)
    fun t ⟨tk, tm, tb⟩ => ⟨?_, ?_, ?_, ?_⟩
  · rw [tk.1 _ (by decide), hv.other _ (by decide), hu.gpr]
  · exact (hu.rest (by simp)).trans ((hv.rest (by simp)).trans (tk.mono (by simp)))
  · rw [hv.mem, hu.mem] at tm; exact tm
  · rw [hv.mem, hu.mem] at tb; exact tb

end VG.Proof.Ed448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.VerifyChecks`. -/
section

/-!
# Ed448 verification's equation on x86 (32-bit): accumulating checks

The word at `BAD` accumulates checks: a check of `P` ORs into it a word below
`2^16` that is 0 exactly when `P` holds (`BadUpd`). Comparing the limbs of
slot 1 with those of another slot (`diffSlot_ok`), and two slots' field
elements, fully reduced (`eqSlots_ok`). `CKeep` is what the comparisons and
the field programs may change: the field operations' registers, the counter
`esi`, and the working space at `BAD`, in the slots and from `ACC`.
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Impl.Ed448.X86 VG.Proof.X448.X86 VG.Proof.X448.Radix16
open VG.Impl.X448.X86 (slot X2 ACC TMP ld copy freeze)

/-! ## The accumulated word -/

/-- `b'` is `b` ORed with a word below `2^16` that is 0 exactly when `P` holds. -/
def BadUpd (P : Prop) (b b' : BitVec 32) : Prop :=
  ∃ c : BitVec 32, c.toNat < 65536 ∧ (c = 0 ↔ P) ∧ b' = b ||| c

theorem BadUpd.trans {P Q : Prop} {b b' b'' : BitVec 32} (h : VG.Proof.Ed448.X86.BadUpd P b b') (h' : VG.Proof.Ed448.X86.BadUpd Q b' b'') :
    VG.Proof.Ed448.X86.BadUpd (P ∧ Q) b b'' := by
  obtain ⟨c, hc, hp, rfl⟩ := h
  obtain ⟨c', hc', hq, rfl⟩ := h'
  refine ⟨c ||| c', ?_, ?_, BitVec.or_assoc _ _ _⟩
  · rw [BitVec.toNat_or]; exact Nat.or_lt_two_pow (n := 16) hc hc'
  · rw [← hp, ← hq]; exact BitVec.or_eq_zero_iff

theorem BadUpd.congr {P Q : Prop} {b b' : BitVec 32} (h : VG.Proof.Ed448.X86.BadUpd P b b') (e : P ↔ Q) : VG.Proof.Ed448.X86.BadUpd Q b b' := by
  obtain ⟨c, hc, hp, rfl⟩ := h
  exact ⟨c, hc, hp.trans e, rfl⟩

theorem BadUpd.rfl' {b : BitVec 32} : VG.Proof.Ed448.X86.BadUpd True b b :=
  ⟨0, by decide, ⟨fun _ => trivial, fun _ => rfl⟩, (BitVec.or_zero).symm⟩

theorem BadUpd.of_eq {P : Prop} {b b' b'' : BitVec 32} (h : VG.Proof.Ed448.X86.BadUpd P b b') (e : b'' = b') :
    VG.Proof.Ed448.X86.BadUpd P b b'' := e ▸ h

theorem BadUpd.zero {P : Prop} {b : BitVec 32} (h : VG.Proof.Ed448.X86.BadUpd P 0 b) : (b = 0 ↔ P) ∧ b.toNat < 65536 := by
  obtain ⟨c, hc, hp, rfl⟩ := h
  have e : (0 : BitVec 32) ||| c = c := BitVec.zero_or
  rw [e]
  exact ⟨hp, hc⟩

/-- The working space changes only at `BAD`, in the slots and from `ACC`. -/
def BMem (base : Addr) (m m' : Mem) : Prop :=
  ∀ p, (ofs base p < BAD ∨ BAD + 4 ≤ ofs base p) → (ofs base p < 64 ∨ 2880 ≤ ofs base p) →
    (ofs base p < ACC ∨ ACC + 512 ≤ ofs base p) → m' p = m p

theorem BMem.refl (base : Addr) (m : Mem) : VG.Proof.Ed448.X86.BMem base m m := fun _ _ _ _ => rfl

theorem BMem.trans {base : Addr} {m₁ m₂ m₃ : Mem} (h₁ : VG.Proof.Ed448.X86.BMem base m₁ m₂) (h₂ : VG.Proof.Ed448.X86.BMem base m₂ m₃) :
    VG.Proof.Ed448.X86.BMem base m₁ m₃ := fun p a b c => (h₂ p a b c).trans (h₁ p a b c)

theorem BMem.of_outside2 {base : Addr} {m m' : Mem} (h : Outside2 base 64 2816 ACC 512 m m') :
    VG.Proof.Ed448.X86.BMem base m m' := fun p _ hb hc => h p hb hc

theorem BMem.of_bad {base : Addr} {m m' : Mem} (h : Outside base BAD 4 m m') : VG.Proof.Ed448.X86.BMem base m m' :=
  fun p ha _ _ => h p ha

theorem BMem.widen {base : Addr} {m m' : Mem} (h : VG.Proof.Ed448.X86.BMem base m m') : Outside2 base 16 2864 ACC 512 m m' :=
  fun p ha hc => h p (by simp only [BAD]; omega) (by omega) hc

theorem BMem.word {base : Addr} {m m' : Mem} (h : VG.Proof.Ed448.X86.BMem base m m') {d : Nat}
    (hb : d + 4 ≤ BAD ∨ BAD + 4 ≤ d) (hs : d + 4 ≤ 64 ∨ 2880 ≤ d) (ha : d + 4 ≤ ACC ∨ ACC + 512 ≤ d)
    (hd : d + 4 ≤ 8192) : VG.Proof.X448.X86.word m' base d = VG.Proof.X448.X86.word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [ofs_off base (by omega)]; omega)
    (by rw [ofs_off base (by omega)]; omega) (by rw [ofs_off base (by omega)]; omega)).symm).symm

/-- What comparisons and field programs may change. -/
structure CKeep (base : Addr) (s t : State) : Prop where
  regs : Keeps (.esi :: workRegs) s t
  mem : VG.Proof.Ed448.X86.BMem base s.mem t.mem

theorem CKeep.refl (base : Addr) (s : State) : VG.Proof.Ed448.X86.CKeep base s s := ⟨Keeps.refl _ _, BMem.refl _ _⟩

theorem CKeep.trans {base : Addr} {s t u : State} (h : VG.Proof.Ed448.X86.CKeep base s t) (h' : VG.Proof.Ed448.X86.CKeep base t u) :
    VG.Proof.Ed448.X86.CKeep base s u := ⟨h.regs.trans h'.regs, h.mem.trans h'.mem⟩

theorem CKeep.toV {base : Addr} {s t : State} (h : VG.Proof.Ed448.X86.CKeep base s t) : VG.Proof.Ed448.X86.VKeep base s t :=
  ⟨h.regs, h.mem.widen⟩

theorem CKeep.scr {base : Addr} {s t : State} (h : VG.Proof.Ed448.X86.CKeep base s t) (hs : Scr s base) : Scr t base :=
  hs.of_keeps h.regs (by decide)

theorem IKeep.toC {base : Addr} {s t : State} (h : IKeep base s t) : VG.Proof.Ed448.X86.CKeep base s t :=
  ⟨h.regs, BMem.of_outside2 h.mem⟩

theorem Keep.toC {base : Addr} {s t : State} (h : VG.Proof.X448.X86.Keep base s t) : VG.Proof.Ed448.X86.CKeep base s t := IKeep.toC h.ikeep

/-! ## What the field programs keep -/

theorem Keep.bad {base : Addr} {s t : State} (h : VG.Proof.X448.X86.Keep base s t) :
    VG.Proof.X448.X86.word t.mem base BAD = VG.Proof.X448.X86.word s.mem base BAD :=
  h.mem.word (Or.inl (by decide)) (Or.inl (by decide)) (by decide)

theorem IKeep.bad {base : Addr} {s t : State} (h : IKeep base s t) :
    VG.Proof.X448.X86.word t.mem base BAD = VG.Proof.X448.X86.word s.mem base BAD :=
  h.mem.word (Or.inl (by decide)) (Or.inl (by decide)) (by decide)

theorem CKeep.sign {base : Addr} {s t : State} (h : VG.Proof.Ed448.X86.CKeep base s t) :
    VG.Proof.X448.X86.word t.mem base SIGN = VG.Proof.X448.X86.word s.mem base SIGN :=
  h.mem.word (Or.inr (by decide)) (Or.inl (by decide)) (Or.inl (by decide)) (by decide)

theorem orBad_ok {s : State} {base : Addr} (hs : Scr s base) {r : Reg} (hre : r ≠ .edi) {P : Prop}
    (hc : (s.gpr r).toNat < 65536) (hp : s.gpr r = 0 ↔ P) :
    WP isa (.block (orBad r)) s fun t =>
      VG.Proof.Ed448.X86.BadUpd P (VG.Proof.X448.X86.word s.mem base BAD) (VG.Proof.X448.X86.word t.mem base BAD) ∧ Outside base BAD 4 s.mem t.mem ∧
        Keeps [r] s t := by
  unfold orBad
  refine wp_alu (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (VG.Proof.Ed448.X86.rd_sc hs (by decide)) fun u hu _ => ?_
  refine store_ok (hs.of_upd hu (Ne.symm hre)) (by decide) fun v hv => WP.block_nil ⟨?_, ?_, ?_⟩
  · refine ⟨s.gpr r, hc, hp, ?_⟩
    rw [hv.mem, hu.mem, hu.gpr]
    change (s.mem.writeW (off base BAD) (s.gpr r ||| word s.mem base BAD)).readW (off base BAD) 32 = _
    rw [Mem.readW_writeW_self32]
    exact BitVec.or_comm _ _
  · rw [hv.mem, hu.mem]; exact writeW_outside _ _ _ (by decide)
  · exact (hu.rest (by simp)).trans (hv.rest _)

/-! ## Comparing limbs -/

theorem xor_limb {x y : BitVec 32} (hx : x.toNat < VG.Proof.X448.Radix16.radix) (hy : y.toNat < VG.Proof.X448.Radix16.radix) :
    (x ^^^ y).toNat < 65536 ∧ (x ^^^ y = 0 ↔ x.toNat = y.toNat) := by
  refine ⟨?_, BitVec.xor_eq_zero_iff.trans ⟨fun h => h ▸ rfl, BitVec.eq_of_toNat_eq⟩⟩
  rw [BitVec.toNat_xor]; exact Nat.xor_lt_two_pow (n := 16) hx hy

theorem diffLimb_ok {s : State} {base : Addr} (hs : Scr s base) {a i : Nat} (ha : a + 112 ≤ 4096)
    (hi : i < 28) :
    WP isa (.block (diffLimb a i)) s fun t =>
      t.gpr .ecx = s.gpr .ecx ||| (VG.Proof.X448.X86.word s.mem base (VG.Impl.X448.X86.X2 + 4 * i) ^^^ VG.Proof.X448.X86.word s.mem base (a + 4 * i)) ∧
        t.mem = s.mem ∧ Keeps [.eax, .ecx] s t := by
  unfold diffLimb
  refine load_ok hs (by simp only [VG.Impl.X448.X86.X2, slot]; omega) fun u hu => ?_
  have us := hs.of_upd hu (by decide)
  refine wp_alu (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) (VG.Proof.Ed448.X86.rd_sc us (by omega)) fun v hv _ => ?_
  refine wp_alu (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) rfl fun w hw _ => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [hw.gpr]
    change v.gpr .ecx ||| v.gpr .eax = _
    rw [hv.gpr, hv.other _ (by decide), hu.other _ (by decide), hu.gpr, hu.mem]
    rfl
  · rw [hw.mem, hv.mem, hu.mem]
  · exact (hu.rest (by simp)).trans ((hv.rest (by simp)).trans (hw.rest (by simp)))

theorem diffSlot_ok {s : State} {base : Addr} (hs : Scr s base) {a : Nat} (ha : a + 112 ≤ 4096)
    (h1 : Bounded s.mem base VG.Impl.X448.X86.X2) (h2 : Bounded s.mem base a) :
    WP isa (.block (diffSlot a)) s fun t =>
      VG.Proof.Ed448.X86.BadUpd (∀ i < 28, limbs s.mem base VG.Impl.X448.X86.X2 i = limbs s.mem base a i) (VG.Proof.X448.X86.word s.mem base BAD)
        (VG.Proof.X448.X86.word t.mem base BAD) ∧ Outside base BAD 4 s.mem t.mem ∧ Keeps [.eax, .ecx] s t := by
  unfold diffSlot
  refine VG.Proof.X448.X86.wp_mov rfl fun u hu => ?_
  have us := hs.of_upd hu (by decide)
  let inv := fun n (t : State) =>
    (t.gpr .ecx).toNat < 65536 ∧ (t.gpr .ecx = 0 ↔ ∀ i < n, limbs s.mem base VG.Impl.X448.X86.X2 i = limbs s.mem base a i) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ecx] s t
  change WP isa (.block ((List.range 28).flatMap (diffLimb a) ++ orBad .ecx)) u _
  rw [WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (N := 28) inv (fun n t hn ⟨tb, tz, tm, tk⟩ => ?_) 28
    (by decide) u ⟨by rw [hu.gpr]; decide, by rw [hu.gpr]; exact ⟨fun _ _ h => absurd h (Nat.not_lt_zero _),
      fun _ => rfl⟩, hu.mem, hu.rest (by simp)⟩) fun t ⟨tb, tz, tm, tk⟩ => ?_
  · refine WP.mono (VG.Proof.Ed448.X86.diffLimb_ok (hs.of_keeps tk (by decide)) ha hn) fun v ⟨vc, vm, vk⟩ => ?_
    rw [tm] at vc
    have x := VG.Proof.Ed448.X86.xor_limb (h1 n hn) (h2 n hn)
    refine ⟨?_, ?_, vm.trans tm, tk.trans (vk.mono (by simp))⟩
    · rw [vc, BitVec.toNat_or]; exact Nat.or_lt_two_pow (n := 16) tb x.1
    · rw [vc]
      refine BitVec.or_eq_zero_iff.trans ((and_congr tz x.2).trans ?_)
      constructor
      · rintro ⟨h, h'⟩ i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact h i hi
        · exact h'
      · intro h
        exact ⟨fun i hi => h i (by omega), h n (by omega)⟩
  · refine WP.mono (VG.Proof.Ed448.X86.orBad_ok (hs.of_keeps tk (by decide)) (by decide) tb tz) fun v ⟨vb, vo, vk⟩ => ?_
    rw [tm] at vb vo
    exact ⟨vb, vo, tk.trans (vk.mono (by simp))⟩

/-! ## Comparing field elements -/

theorem valN_inj {f g : Nat → Nat} :
    ∀ {n}, (∀ i < n, f i < VG.Proof.X448.Radix16.radix) → (∀ i < n, g i < VG.Proof.X448.Radix16.radix) → VG.Proof.X448.Radix16.valN f n = VG.Proof.X448.Radix16.valN g n → ∀ i < n, f i = g i
  | 0, _, _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, hf, hg, h, i, hi => by
    rw [VG.Proof.X448.Radix16.valN_succ, VG.Proof.X448.Radix16.valN_succ] at h
    have lf := VG.Proof.X448.Radix16.valN_lt (n := n) (fun j hj => hf j (by omega))
    have lg := VG.Proof.X448.Radix16.valN_lt (n := n) (fun j hj => hg j (by omega))
    have hp : 0 < VG.Proof.X448.Radix16.radix ^ n := Nat.pow_pos (by decide)
    have e1 : f n = g n := by
      have := congrArg (· / VG.Proof.X448.Radix16.radix ^ n) h
      simp only [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt lf, Nat.div_eq_of_lt lg, Nat.zero_add] at this
      exact this
    rw [e1] at h
    have e0 : VG.Proof.X448.Radix16.valN f n = VG.Proof.X448.Radix16.valN g n := by omega
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact VG.Proof.Ed448.X86.valN_inj (fun j hj => hf j (by omega)) (fun j hj => hg j (by omega)) e0 i hi
    · exact e1

theorem limbs_eq_iff {m : Mem} {base : Addr} {a b : Nat} (ha : Bounded m base a) (hb : Bounded m base b) :
    (∀ i < 28, limbs m base a i = limbs m base b i) ↔ VG.Proof.X448.X86.fe m base a = VG.Proof.X448.X86.fe m base b :=
  ⟨fun h => VG.Proof.X448.Radix16.valN_congr h, fun h => VG.Proof.Ed448.X86.valN_inj ha hb h⟩

theorem outB {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') (h1 : 64 ≤ o)
    (h2 : o + n ≤ 2880) : VG.Proof.Ed448.X86.BMem base m m' := fun p _ hp _ => h p (by omega)

theorem fmB {base : Addr} {o : Nat} {m m' : Mem} (h : FieldMem base o m m') (h1 : 64 ≤ o)
    (h2 : o + 112 ≤ 2880) : VG.Proof.Ed448.X86.BMem base m m' := fun p _ hp hq => h p (by omega) hq

/-- Slots `a` and `b` compared: `BAD |= 0` exactly when they hold the same field
element; slot `a` holds the same element, fully reduced, and slot 1 is
overwritten. -/
theorem eqSlots_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (a b : Index)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) :
    WP isa (.block (eqSlots (slot a.val) (slot b.val))) s fun t =>
      VG.Proof.Ed448.X86.CKeep base s t ∧ BoundedEnv t.mem base ∧ (∀ i : Index, i ≠ 1 → VG.Proof.X448.X86.E t.mem base i = VG.Proof.X448.X86.E s.mem base i) ∧
        VG.Proof.Ed448.X86.BadUpd (VG.Proof.X448.X86.E s.mem base a = VG.Proof.X448.X86.E s.mem base b) (VG.Proof.X448.X86.word s.mem base BAD) (VG.Proof.X448.X86.word t.mem base BAD) := by
  have sa := VG.Proof.Ed448.X86.slot_range a
  have sb := VG.Proof.Ed448.X86.slot_range b
  have hX2v : VG.Impl.X448.X86.X2 = 192 := rfl
  have hA : ACC = 3584 := rfl
  have hX2 : VG.Impl.X448.X86.X2 = slot (1 : Index).val := rfl
  have s1a : slot a.val + 112 ≤ VG.Impl.X448.X86.X2 ∨ VG.Impl.X448.X86.X2 + 112 ≤ slot a.val := by rw [hX2]; exact slot_sep ha1
  have s1b : slot b.val + 112 ≤ VG.Impl.X448.X86.X2 ∨ VG.Impl.X448.X86.X2 + 112 ≤ slot b.val := by rw [hX2]; exact slot_sep hb1
  have sab := slot_sep hab
  unfold eqSlots
  simp only [List.append_assoc]
  -- slot 1 = slot a
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.copy_ok hs (o := VG.Impl.X448.X86.X2) (a := slot a.val) (by decide) (by omega)
    (Or.inr (by omega))) fun s1 ⟨f1, m1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  have bd1 : Bounded s1.mem base VG.Impl.X448.X86.X2 := fun i hi => by rw [f1 i hi]; exact hb a i hi
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.freeze_ok hs1 bd1) fun s2 ⟨b2, v2, m2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  -- slot a = slot 1
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.copy_ok hs2 (o := slot a.val) (a := VG.Impl.X448.X86.X2) (by omega) (by decide)
    (Or.inr (by omega))) fun s3 ⟨f3, m3, k3⟩ => ?_
  have hs3 := hs2.of_keeps k3 (by decide)
  -- slot 1 = slot b
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.copy_ok hs3 (o := VG.Impl.X448.X86.X2) (a := slot b.val) (by decide) (by omega)
    (Or.inr (by omega))) fun s4 ⟨f4, m4, k4⟩ => ?_
  have hs4 := hs3.of_keeps k4 (by decide)
  have lb3 : ∀ i < 28, limbs s3.mem base (slot b.val) i = limbs s.mem base (slot b.val) i := by
    intro i hi
    rw [m3.limbs (by omega) (by omega) hi, m2.limbs s1b (by omega) hi,
      m1.limbs (by omega) (by omega) hi]
  have bd4 : Bounded s4.mem base VG.Impl.X448.X86.X2 := fun i hi => by rw [f4 i hi, lb3 i hi]; exact hb b i hi
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.freeze_ok hs4 bd4) fun s5 ⟨b5, v5, m5, k5⟩ => ?_
  have hs5 := hs4.of_keeps k5 (by decide)
  have la5 : ∀ i < 28, limbs s5.mem base (slot a.val) i = limbs s2.mem base VG.Impl.X448.X86.X2 i := by
    intro i hi
    rw [m5.limbs s1a (by omega) hi, m4.limbs (by omega) (by omega) hi, f3 i hi]
  have ba5 : Bounded s5.mem base (slot a.val) := fun i hi => by rw [la5 i hi]; exact b2 i hi
  refine WP.mono (VG.Proof.Ed448.X86.diffSlot_ok hs5 (by omega) b5 ba5) fun t ⟨tb, tm, tk⟩ => ?_
  have fa : VG.Proof.X448.X86.fe s5.mem base (slot a.val) = VG.Proof.X448.X86.fe s.mem base (slot a.val) % Spec.X448.P := by
    rw [show VG.Proof.X448.X86.fe s5.mem base (slot a.val) = VG.Proof.X448.X86.fe s2.mem base VG.Impl.X448.X86.X2 from VG.Proof.X448.Radix16.valN_congr la5, v2]
    exact congrArg (· % Spec.X448.P) (VG.Proof.X448.Radix16.valN_congr f1)
  have fb : VG.Proof.X448.X86.fe s5.mem base VG.Impl.X448.X86.X2 = VG.Proof.X448.X86.fe s.mem base (slot b.val) % Spec.X448.P := by
    rw [v5]; exact congrArg (· % Spec.X448.P) ((VG.Proof.X448.Radix16.valN_congr f4).trans (VG.Proof.X448.Radix16.valN_congr lb3))
  have tl : ∀ d, 64 ≤ d → d + 112 ≤ 2880 → ∀ j < 28, limbs t.mem base d j = limbs s5.mem base d j :=
    fun d h1 h2 j hj => tm.limbs (Or.inr (by simp only [BAD]; omega)) (by omega) hj
  have other : ∀ i : Index, i ≠ 1 → i ≠ a → ∀ j < 28,
      limbs t.mem base (slot i.val) j = limbs s.mem base (slot i.val) j := by
    intro i hi1 hia j hj
    have si := VG.Proof.Ed448.X86.slot_range i
    have s1i : slot i.val + 112 ≤ VG.Impl.X448.X86.X2 ∨ VG.Impl.X448.X86.X2 + 112 ≤ slot i.val := by rw [hX2]; exact slot_sep hi1
    have sai := slot_sep hia
    rw [tl _ si.1 si.2 j hj, m5.limbs s1i (by omega) hj, m4.limbs (by omega) (by omega) hj,
      m3.limbs (by omega) (by omega) hj, m2.limbs s1i (by omega) hj,
      m1.limbs (by omega) (by omega) hj]
  refine ⟨⟨?_, ?_⟩, fun i j hj => ?_, fun i hi => ?_, ?_⟩
  · refine (((k1.mono ?_).trans ((k2.mono ?_).trans ((k3.mono ?_).trans ((k4.mono ?_).trans
      (k5.mono ?_))))).trans (tk.mono ?_)) <;> intro r hr <;> revert r <;> decide
  · exact (((((VG.Proof.Ed448.X86.outB m1 (by decide) (by decide)).trans (VG.Proof.Ed448.X86.fmB m2 (by decide) (by decide))).trans
      (VG.Proof.Ed448.X86.outB m3 (by omega) (by omega))).trans (VG.Proof.Ed448.X86.outB m4 (by decide) (by decide))).trans
      (VG.Proof.Ed448.X86.fmB m5 (by decide) (by decide))).trans (BMem.of_bad tm)
  · have si := VG.Proof.Ed448.X86.slot_range i
    rw [tl _ si.1 si.2 j hj]
    by_cases h1 : i = 1
    · subst i; exact b5 j hj
    · by_cases ha' : i = a
      · subst i; exact ba5 j hj
      · rw [← tl _ si.1 si.2 j hj, other i h1 ha' j hj]; exact hb i j hj
  · by_cases ha' : i = a
    · subst i
      simp only [VG.Proof.X448.X86.E, VG.Proof.X448.X86.F]
      rw [show VG.Proof.X448.X86.fe t.mem base (slot a.val) = VG.Proof.X448.X86.fe s5.mem base (slot a.val) from
        VG.Proof.X448.Radix16.valN_congr (tl _ sa.1 sa.2), fa, Proof.X448.toFe_mod]
    · simp only [VG.Proof.X448.X86.E, VG.Proof.X448.X86.F]
      exact congrArg Proof.X448.toFe (VG.Proof.X448.Radix16.valN_congr (other i hi ha'))
  · have bad5 : VG.Proof.X448.X86.word s5.mem base BAD = VG.Proof.X448.X86.word s.mem base BAD := by
      rw [m5.word (Or.inl (by simp only [BAD]; omega)) (by simp only [BAD, ACC]; omega),
        m4.word (Or.inl (by simp only [BAD]; omega)) (by decide),
        m3.word (Or.inl (by simp only [BAD]; omega)) (by decide),
        m2.word (Or.inl (by simp only [BAD]; omega)) (by simp only [BAD, ACC]; omega),
        m1.word (Or.inl (by simp only [BAD]; omega)) (by decide)]
    rw [bad5] at tb
    refine tb.congr ?_
    rw [VG.Proof.Ed448.X86.limbs_eq_iff b5 ba5, fb, fa]
    simp only [VG.Proof.X448.X86.E, VG.Proof.X448.X86.F, Proof.X448.toFe_eq_iff]
    exact eq_comm

end VG.Proof.Ed448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.VerifyS`. -/
section

/-!
# Ed448 verification's equation on x86 (32-bit): limbs from bytes, and `S < L`

`byteLimb_ok`: a limb of 56 bytes from two byte loads. `sCheck_ok`: the
twenty-eight limbs of `S`'s low 448 bits plus those of `2^448 - L` (scalar
reduction's `kLimb`), carried by X448's `pass`, carry out of 448 bits exactly
when they are at least `L`; with byte 56, `BAD |= 0` exactly when `S < L`.
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Impl.Ed448.X86 VG.Proof.X448.X86 VG.Proof.X448.Radix16
open VG.Impl.X448.X86 (slot X2 ACC TMP ld st pass at_)

/-- The number of 57 bytes: the limbs of the first 56 and the last byte. -/
theorem decodeLE_bytes57 (m : Mem) (q : Addr) :
    Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m q 57) =
      VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.decoded m q) 28 + 256 ^ 56 * (m (q + BitVec.ofNat 64 56)).toNat := by
  rw [Limbs16.bytesAt_57 m q, Proof.Ed448.decodeLE_append, Proof.Ed448.decodeLE_eq, Proof.Ed448.decodeLE_eq,
    show (56 : Nat) = 2 * 28 from rfl, VG.Proof.X448.Radix16.decoded_val m q 28, Proof.X448.length_bytesAt]
  simp only [Proof.X25519.leNum, Nat.mul_zero, Nat.add_zero]

/-- The address of byte `src + j` at `esi`. -/
theorem ea_esi {s : State} {q : Addr} {src : Nat} (hq : (s.gpr .esi).setWidth 64 + BitVec.ofNat 64 src = q)
    {j : Nat} (hfit : (s.gpr .esi).toNat + src + j < 2 ^ 32) :
    s.ea (VG.Impl.X448.X86.at_ .esi (src + j)) = q + BitVec.ofNat 64 j := by
  change VG.X86.addr (s.gpr .esi) (src + j) = _
  rw [addr_eq (by omega), ← hq, Offset.add_add]

theorem byteLimb_ok {s : State} {q : Addr} {src : Nat}
    (hq : (s.gpr .esi).setWidth 64 + BitVec.ofNat 64 src = q) (hfit : (s.gpr .esi).toNat + src + 56 ≤ 2 ^ 32)
    {i : Nat} (hi : i < 28) (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 j) 1) :
    WP isa (.block (byteLimb src i)) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (VG.Proof.X448.Radix16.decoded s.mem q i) ∧ t.mem = s.mem ∧ Keeps [.eax, .edx] s t := by
  unfold byteLimb
  refine wp_load8 (a := q + BitVec.ofNat 64 (2 * i)) (VG.Proof.Ed448.X86.ea_esi hq (by omega))
    (hr _ (by omega)) fun s1 h1 => ?_
  refine wp_load8 (a := q + BitVec.ofNat 64 (2 * i + 1))
    (by rw [show src + 2 * i + 1 = src + (2 * i + 1) by omega]
        exact VG.Proof.Ed448.X86.ea_esi (by rw [h1.other .esi (by decide)]; exact hq) (by rw [h1.other .esi (by decide)]; omega))
    (by rw [h1.rd, h1.wr]; exact hr _ (by omega)) fun s2 h2 => ?_
  refine wp_shift (by decide) fun sr hrot => ?_
  refine wp_alu (by simp [plain]) rfl fun s3 h3 _ => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [h3.gpr]
    change sr.gpr .eax + sr.gpr .edx = _
    rw [hrot.other .eax (by decide), hrot.gpr]
    rw [h2.other .eax (by decide), h1.gpr, h2.gpr, h1.mem, byte_rotate]
    apply BitVec.eq_of_toNat_eq
    have h0 := (s.mem (q + BitVec.ofNat 64 (2 * i))).isLt
    have h1 := (s.mem (q + BitVec.ofNat 64 (2 * i + 1))).isLt
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
      Nat.shiftLeft_eq, BitVec.toNat_ofNat, VG.Proof.X448.Radix16.decoded, byteN]
    omega
  · rw [h3.mem, hrot.mem, h2.mem, h1.mem]
  · exact (h1.rest (by simp)).trans ((h2.rest (by simp)).trans ((hrot.rest (by simp)).trans
      (h3.rest (by simp))))

theorem sLimb_ok {s : State} {base q : Addr} (hs : Scr s base)
    (hq : (s.gpr .esi).setWidth 64 + BitVec.ofNat 64 57 = q) (hfit : (s.gpr .esi).toNat + 114 ≤ 2 ^ 32)
    {i : Nat} (hi : i < 28) (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 j) 1) :
    WP isa (.block (sLimb i)) s fun t =>
      t.mem = s.mem.writeW (off base (TMP + 4 * i)) (BitVec.ofNat 32 (VG.Proof.X448.Radix16.decoded s.mem q i + kLimb i)) ∧
        Keeps [.eax, .edx] s t := by
  unfold sLimb
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86.byteLimb_ok hq (by omega) hi hr) fun t ⟨ta, tm, tk⟩ => ?_
  have ht := hs.of_keeps tk (by decide)
  refine wp_alu (Or.inl rfl) rfl fun u hu _ => ?_
  refine store_ok (ht.of_upd hu (by decide)) (by simp only [TMP]; omega) fun w hw =>
    WP.block_nil ⟨?_, tk.trans ((hu.rest (by simp)).trans (hw.rest _))⟩
  rw [hw.mem, hu.mem, tm, hu.gpr]
  change s.mem.writeW _ (t.gpr .eax + BitVec.ofNat 32 (kLimb i)) = _
  rw [ta]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have := decoded_lt s.mem q i
  have := kLimb_lt i
  simp only [VG.Proof.X448.Radix16.radix] at *
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem sLimbs_ok {s : State} {base q : Addr} (hs : Scr s base)
    (hq : (s.gpr .esi).setWidth 64 + BitVec.ofNat 64 57 = q) (hfit : (s.gpr .esi).toNat + 114 ≤ 2 ^ 32)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 j) 1)
    (hd : ∀ j < 56, 8192 ≤ ofs base (q + BitVec.ofNat 64 j)) :
    WP isa (.block ((List.range 28).flatMap sLimb)) s fun t =>
      (∀ i < 28, limbs t.mem base TMP i = VG.Proof.X448.Radix16.decoded s.mem q i + kLimb i) ∧
        Outside base TMP 112 s.mem t.mem ∧ Keeps [.eax, .edx] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base TMP i = VG.Proof.X448.Radix16.decoded s.mem q i + kLimb i) ∧
      Outside base TMP 112 s.mem t.mem ∧ Keeps [.eax, .edx] s t
  refine wp_range_flatMap (M := isa) (N := 28) inv (fun n t hn ⟨tf, tm, tk⟩ => ?_) 28 (by decide) s
    ⟨fun _ h => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩
  have byte : ∀ j < 56, t.mem (q + BitVec.ofNat 64 j) = s.mem (q + BitVec.ofNat 64 j) :=
    fun j hj => tm _ (Or.inr (by have := hd j hj; simp only [TMP]; omega))
  have eq : VG.Proof.X448.Radix16.decoded t.mem q n = VG.Proof.X448.Radix16.decoded s.mem q n := by
    simp only [VG.Proof.X448.Radix16.decoded, byteN]; rw [byte _ (by omega), byte _ (by omega)]
  refine WP.mono (VG.Proof.Ed448.X86.sLimb_ok (q := q) (hs.of_keeps tk (by decide)) (by rw [tk.1 _ (by decide)]; exact hq)
    (by rw [tk.1 _ (by decide)]; exact hfit) hn (by rw [tk.2.1, tk.2.2]; exact hr))
    fun u ⟨um, uk⟩ => ⟨fun i hi => ?_, tm.trans ?_, tk.trans uk⟩
  · rw [eq] at um
    change (VG.Proof.X448.X86.word u.mem base (TMP + 4 * i)).toNat = _
    rw [um, word_write t.mem base (by simp only [TMP]; omega) (by simp only [TMP]; omega)]
    by_cases h : i = n
    · have := decoded_lt s.mem q n
      have := kLimb_lt n
      simp only [VG.Proof.X448.Radix16.radix] at *
      rw [ite_eq_left h, h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · rw [ite_eq_right h]; exact tf i (by omega)
  · rw [um]; exact (writeW_outside _ _ _ (by simp only [TMP]; omega)).mono (by omega) (by omega)

theorem radix_28 : VG.Proof.X448.Radix16.radix ^ 28 = 2 ^ 448 := by decide +kernel

theorem sCheck_ok {s : State} {base q : Addr} (hs : Scr s base)
    (hq : (s.gpr .esi).setWidth 64 + BitVec.ofNat 64 57 = q) (hfit : (s.gpr .esi).toNat + 114 ≤ 2 ^ 32)
    (hr : ∀ j < 57, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 j) 1)
    (hd : ∀ j < 57, 8192 ≤ ofs base (q + BitVec.ofNat 64 j)) :
    WP isa (.block sCheck) s fun t =>
      VG.Proof.Ed448.X86.BadUpd (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem q 57) < Spec.Ed448.L) (VG.Proof.X448.X86.word s.mem base BAD)
        (VG.Proof.X448.X86.word t.mem base BAD) ∧ Outside2 base TMP 112 BAD 4 s.mem t.mem ∧ Keeps [.eax, .ebx, .edx] s t := by
  unfold sCheck
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86.sLimbs_ok hs hq hfit (fun j hj => hr j (by omega)) (fun j hj => hd j (by omega)))
    fun t ⟨tf, tm, tk⟩ => ?_
  have ht := hs.of_keeps tk (by decide)
  have hf : ∀ i < 28, VG.Proof.X448.Radix16.decoded s.mem q i + kLimb i ≤ 2 ^ 32 - VG.Proof.X448.Radix16.radix := fun i _ => by
    have := decoded_lt s.mem q i; have := kLimb_lt i; simp only [VG.Proof.X448.Radix16.radix] at *; omega
  rw [WP.block_append_iff]
  refine WP.mono (pass_ok ht (o := TMP) (a := TMP) (by decide) (by decide) (Or.inl rfl) tf hf)
    fun u ⟨_, uc, um, uk⟩ => ?_
  have hu := ht.of_keeps uk (by decide)
  have esi : u.gpr .esi = s.gpr .esi := by rw [uk.1 _ (by decide), tk.1 _ (by decide)]
  have b56 : u.mem (q + BitVec.ofNat 64 56) = s.mem (q + BitVec.ofNat 64 56) := by
    have := hd 56 (by decide)
    rw [um _ (Or.inr (by simp only [TMP]; omega)), tm _ (Or.inr (by simp only [TMP]; omega))]
  refine wp_load8 (a := q + BitVec.ofNat 64 56)
    (by rw [show (113 : Nat) = 57 + 56 from rfl]; exact VG.Proof.Ed448.X86.ea_esi (by rw [esi]; exact hq) (by rw [esi]; omega))
    (by rw [uk.2.1, uk.2.2, tk.2.1, tk.2.2]; exact hr 56 (by decide)) fun v hv => ?_
  refine wp_alu (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) rfl fun w hw _ => ?_
  -- the carry and the check
  have cy := VG.Proof.X448.Radix16.pass_eq (fun i => VG.Proof.X448.Radix16.decoded s.mem q i + kLimb i) 28
  rw [VG.Proof.X448.Radix16.valN_add, valN_kLimb, VG.Proof.Ed448.X86.radix_28] at cy
  have dl : VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.digit fun i => VG.Proof.X448.Radix16.decoded s.mem q i + kLimb i) 28 < 2 ^ 448 := by
    rw [← VG.Proof.Ed448.X86.radix_28]; exact VG.Proof.X448.Radix16.valN_lt (fun i _ => VG.Proof.X448.Radix16.digit_lt _ i)
  have yl : VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.decoded s.mem q) 28 < 2 ^ 448 := by
    rw [← VG.Proof.Ed448.X86.radix_28]; exact VG.Proof.X448.Radix16.valN_lt (fun i _ => decoded_lt _ _ i)
  have hL : Spec.Ed448.L ≤ 2 ^ 448 := by decide +kernel
  have c1 : VG.Proof.X448.Radix16.carry (fun i => VG.Proof.X448.Radix16.decoded s.mem q i + kLimb i) 28 ≤ 1 := by
    generalize (2 : Nat) ^ 448 = M at *
    generalize VG.Proof.X448.Radix16.carry (fun i => VG.Proof.X448.Radix16.decoded s.mem q i + kLimb i) 28 = c at *
    rcases Nat.lt_or_ge c 2 with h | h
    · omega
    · have : M * 2 ≤ M * c := Nat.mul_le_mul_left M h
      omega
  have hchk := Proof.Ed448.sCheck_nat (b := (s.mem (q + BitVec.ofNat 64 56)).toNat) yl dl c1 cy
  rw [← VG.Proof.Ed448.X86.decodeLE_bytes57] at hchk
  have e3 : w.gpr .eax = (s.mem (q + BitVec.ofNat 64 56)).setWidth 32 |||
      BitVec.ofNat 32 (VG.Proof.X448.Radix16.carry (fun i => VG.Proof.X448.Radix16.decoded s.mem q i + kLimb i) 28) := by
    rw [hw.gpr]; change v.gpr .eax ||| v.gpr .ebx = _
    rw [hv.gpr, hv.other _ (by decide), b56]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [uc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have bt := (s.mem (q + BitVec.ofNat 64 56)).isLt
  have hw' : Scr w base := (hu.of_upd hv (by decide)).of_upd hw (by decide)
  refine WP.mono (VG.Proof.Ed448.X86.orBad_ok (s := w) hw' (by decide)
    (P := Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem q 57) < Spec.Ed448.L) ?_ ?_)
    fun x ⟨xb, xm, xk⟩ => ⟨?_, ?_, ?_⟩
  · rw [e3, BitVec.toNat_or, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    exact Nat.or_lt_two_pow (n := 16) (by omega) (by omega)
  · rw [e3, ← hchk]
    refine BitVec.or_eq_zero_iff.trans ?_
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · have := congrArg BitVec.toNat h2
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        exact this
      · have := congrArg BitVec.toNat h1
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)] at this
        exact this
    · rintro ⟨h1, h2⟩
      refine ⟨BitVec.eq_of_toNat_eq ?_, ?_⟩
      · rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; exact h2
      · rw [h1]
  · have bw : VG.Proof.X448.X86.word w.mem base BAD = VG.Proof.X448.X86.word s.mem base BAD := by
      rw [hw.mem, hv.mem, um.word (Or.inl (by simp only [BAD, TMP]; omega)) (by decide),
        tm.word (Or.inl (by simp only [BAD, TMP]; omega)) (by decide)]
    rw [bw] at xb
    exact xb
  · intro p h1 h2
    rw [xm p h2, hw.mem, hv.mem, um p h1, tm p h1]
  · exact (tk.mono (by simp)).trans ((uk.mono (by simp)).trans ((hv.rest (by simp)).trans
      ((hw.rest (by simp)).trans (xk.mono (by simp)))))

end VG.Proof.Ed448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.VerifyDecodeY`. -/
section

/-!
# Ed448 verification's equation on x86 (32-bit): the `y` of a point

`decodeY_ok`: the 57 bytes of an encoded point at `q` (the argument read from
the stack into `esi`): the twenty-eight limbs of the first 56 (`y₀`) into
slot `yo`, the sign bit (bit 7 of the last byte `b`) to `SIGN`, and
`BAD |= 0` exactly when bits 0–6 of `b` are 0 and `y₀ < p` (`y₀` is equal to
its full reduction, in slot 1).
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Impl.Ed448.X86 VG.Proof.X448.X86 VG.Proof.X448.Radix16
open VG.Impl.X448.X86 (slot X2 ACC TMP ld st copy freeze at_)

theorem loadLimbs_ok {s : State} {base q : Addr} (hs : Scr s base) (hq : (s.gpr .esi).setWidth 64 = q)
    (hfit : (s.gpr .esi).toNat + 57 ≤ 2 ^ 32)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 j) 1)
    (hd : ∀ j < 56, 8192 ≤ ofs base (q + BitVec.ofNat 64 j)) {o : Nat} (ho : 16 ≤ o ∧ o + 112 ≤ 4096) :
    WP isa (.block (loadLimbs o)) s fun t =>
      (∀ i < 28, limbs t.mem base o i = VG.Proof.X448.Radix16.decoded s.mem q i) ∧
        Outside base o 112 s.mem t.mem ∧ Keeps [.eax, .edx] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base o i = VG.Proof.X448.Radix16.decoded s.mem q i) ∧
      Outside base o 112 s.mem t.mem ∧ Keeps [.eax, .edx] s t
  refine wp_range_flatMap (M := isa) (N := 28) inv (fun n t hn ⟨tf, tm, tk⟩ => ?_) 28 (by decide) s
    ⟨fun _ h => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩
  have byte : ∀ j < 56, t.mem (q + BitVec.ofNat 64 j) = s.mem (q + BitVec.ofNat 64 j) :=
    fun j hj => tm _ (Or.inr (by have := hd j hj; omega))
  have eq : VG.Proof.X448.Radix16.decoded t.mem q n = VG.Proof.X448.Radix16.decoded s.mem q n := by
    simp only [VG.Proof.X448.Radix16.decoded, byteN]; rw [byte _ (by omega), byte _ (by omega)]
  have te : t.gpr .esi = s.gpr .esi := tk.1 _ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86.byteLimb_ok (src := 0) (q := q)
    (by rw [te, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero, hq]) (by rw [te]; omega) hn
    (by rw [tk.2.1, tk.2.2]; exact hr)) fun u ⟨u3, um, uk⟩ => ?_
  refine store_ok ((hs.of_keeps tk (by decide)).of_keeps uk (by decide)) (by omega) fun v hv =>
    WP.block_nil ⟨fun i hi => ?_, tm.trans ?_, tk.trans (uk.trans (hv.rest _))⟩
  · change (VG.Proof.X448.X86.word v.mem base (o + 4 * i)).toNat = _
    rw [hv.mem, um, word_write t.mem base (by omega) (by omega)]
    by_cases h : i = n
    · rw [ite_eq_left h, h, u3, eq, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (Nat.lt_trans (decoded_lt s.mem q n) (by decide))]
    · rw [ite_eq_right h]; exact tf i (by omega)
  · rw [hv.mem, um]; exact (writeW_outside _ _ _ (by omega)).mono (by omega) (by omega)

/-- The last byte `b`: `SIGN = b / 128` and `eax = b mod 128`. -/
theorem signByte_ok {s : State} {base q : Addr} (hs : Scr s base) (hq : (s.gpr .esi).setWidth 64 = q)
    (hfit : (s.gpr .esi).toNat + 57 ≤ 2 ^ 32) (hr : InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 56) 1) :
    WP isa (.block signByte) s fun t =>
      (t.gpr .eax).toNat = (s.mem (q + BitVec.ofNat 64 56)).toNat % 128 ∧
      t.mem = s.mem.writeW (off base SIGN) (BitVec.ofNat 32 ((s.mem (q + BitVec.ofNat 64 56)).toNat / 128)) ∧
      Keeps [.eax, .edx] s t := by
  unfold signByte
  refine wp_load8 (a := q + BitVec.ofNat 64 56)
    (by rw [show (56 : Nat) = 0 + 56 from rfl]
        exact VG.Proof.Ed448.X86.ea_esi (by rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero, hq]) (by omega)) hr
    fun u hu => ?_
  refine VG.Proof.X448.X86.wp_mov rfl fun v hv => ?_
  refine wp_shift (by decide) fun w hw => ?_
  have sw := ((hs.of_upd hu (by decide)).of_upd hv (by decide)).of_upd hw (by decide)
  refine store_ok sw (by decide) fun x hx => ?_
  refine wp_alu (Or.inr (Or.inr (Or.inl rfl))) rfl fun y hy _ => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [hy.gpr]; change (x.gpr .eax &&& 0x7f#32).toNat = _
    rw [hx.gpr, hw.other _ (by decide), hv.other _ (by decide), hu.gpr, BitVec.toNat_and,
      BitVec.toNat_setWidth, show (0x7f#32).toNat = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    have := (s.mem (q + BitVec.ofNat 64 56)).isLt
    omega
  · rw [hy.mem, hx.mem, hw.mem, hv.mem, hu.mem, hw.gpr]
    change s.mem.writeW _ (v.gpr .edx >>> 7) = _
    rw [hv.gpr, hu.gpr]
    congr 1
    apply BitVec.eq_of_toNat_eq
    have := (s.mem (q + BitVec.ofNat 64 56)).isLt
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  · exact (hu.rest (by simp)).trans ((hv.rest (by simp)).trans ((hw.rest (by simp)).trans
      ((hx.rest _).trans (hy.rest (by simp)))))

/-- `decodeY d yo`, for the pointer `p` at `[esp + d]`. -/
theorem decodeY_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    {d : Nat} {a : Addr} (ha : s.ea (VG.Impl.X448.X86.at_ .esp d) = a) (har : InRegions (s.rd ++ s.wr) a 4)
    {p : BitVec 32} (hp : s.mem.readW a 32 = p) (hfit : p.toNat + 57 ≤ 2 ^ 32)
    (hr : ∀ j < 57, InRegions (s.rd ++ s.wr) (p.setWidth 64 + BitVec.ofNat 64 j) 1)
    (hd : ∀ j < 57, 8192 ≤ ofs base (p.setWidth 64 + BitVec.ofNat 64 j)) (yo : Index) (hyo : yo ≠ 1) :
    WP isa (.block (decodeY d yo.val)) s fun t =>
      VG.Proof.Ed448.X86.VKeep base s t ∧ BoundedEnv t.mem base ∧
      VG.Proof.X448.X86.word t.mem base SIGN = BitVec.ofNat 32 ((s.mem (p.setWidth 64 + BitVec.ofNat 64 56)).toNat / 128) ∧
      VG.Proof.Ed448.X86.BadUpd ((s.mem (p.setWidth 64 + BitVec.ofNat 64 56)).toNat % 128 = 0 ∧
        VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.decoded s.mem (p.setWidth 64)) 28 < Spec.X448.P) (VG.Proof.X448.X86.word s.mem base BAD) (VG.Proof.X448.X86.word t.mem base BAD) ∧
      VG.Proof.X448.X86.E t.mem base yo = Proof.X448.toFe (VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.decoded s.mem (p.setWidth 64)) 28) ∧
      (∀ i : Index, i ≠ 1 → i ≠ yo → VG.Proof.X448.X86.E t.mem base i = VG.Proof.X448.X86.E s.mem base i) := by
  generalize hq : p.setWidth 64 = q at hr hd ⊢
  have sy := VG.Proof.Ed448.X86.slot_range yo
  have hX2v : VG.Impl.X448.X86.X2 = 192 := rfl
  have hA : ACC = 3584 := rfl
  have hX2 : VG.Impl.X448.X86.X2 = slot (1 : Index).val := rfl
  have s1y : slot yo.val + 112 ≤ VG.Impl.X448.X86.X2 ∨ VG.Impl.X448.X86.X2 + 112 ≤ slot yo.val := by rw [hX2]; exact slot_sep hyo
  unfold decodeY
  simp only [List.append_assoc]
  refine wp_load ha har fun s0 h0 => ?_
  rw [hp] at h0
  have hs0 := hs.of_upd h0 (by decide)
  have hrr : s0.rd ++ s0.wr = s.rd ++ s.wr := by rw [h0.rd, h0.wr]
  simp only [List.append_eq]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86.loadLimbs_ok hs0 (by rw [h0.gpr, hq]) (by rw [h0.gpr]; exact hfit)
    (fun j hj => by rw [hrr]; exact hr j (by omega)) (fun j hj => hd j (by omega))
    (o := slot yo.val) ⟨by omega, by omega⟩) fun s1 ⟨f1, m1, k1⟩ => ?_
  rw [h0.mem] at f1 m1
  have hs1 := hs0.of_keeps k1 (by decide)
  have b56 : s1.mem (q + BitVec.ofNat 64 56) = s.mem (q + BitVec.ofNat 64 56) :=
    m1 _ (Or.inr (by have := hd 56 (by decide); omega))
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86.signByte_ok hs1 (q := q) (by rw [k1.1 _ (by decide), h0.gpr, hq])
    (by rw [k1.1 _ (by decide), h0.gpr]; exact hfit) (by rw [k1.2.1, k1.2.2, hrr]; exact hr 56 (by decide)))
    fun s2 ⟨r2, m2, k2⟩ => ?_
  rw [b56] at r2 m2
  have hs2 := hs1.of_keeps k2 (by decide)
  have o2 : Outside base SIGN 4 s1.mem s2.mem := by rw [m2]; exact writeW_outside _ _ _ (by decide)
  have l2 : ∀ i < 28, limbs s2.mem base (slot yo.val) i = VG.Proof.X448.Radix16.decoded s.mem q i := fun i hi => by
    rw [o2.limbs (Or.inr (by simp only [SIGN]; omega)) (by omega) hi, f1 i hi]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86.orBad_ok (s := s2) hs2 (by decide)
    (P := (s.mem (q + BitVec.ofNat 64 56)).toNat % 128 = 0)
    (by rw [r2]; omega) (by rw [← r2]; exact ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq h⟩))
    fun s3 ⟨b3, m3, k3⟩ => ?_
  have hs3 := hs2.of_keeps k3 (by decide)
  have l3 : ∀ i < 28, limbs s3.mem base (slot yo.val) i = VG.Proof.X448.Radix16.decoded s.mem q i := fun i hi => by
    rw [m3.limbs (Or.inr (by simp only [BAD]; omega)) (by omega) hi, l2 i hi]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.copy_ok hs3 (o := VG.Impl.X448.X86.X2) (a := slot yo.val) (by decide) (by omega)
    (Or.inr (by omega))) fun s4 ⟨f4, m4, k4⟩ => ?_
  have hs4 := hs3.of_keeps k4 (by decide)
  have bd4 : Bounded s4.mem base VG.Impl.X448.X86.X2 := fun i hi => by rw [f4 i hi, l3 i hi]; exact decoded_lt _ _ _
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.freeze_ok hs4 bd4) fun s5 ⟨b5, v5, m5, k5⟩ => ?_
  have hs5 := hs4.of_keeps k5 (by decide)
  have l5 : ∀ i < 28, limbs s5.mem base (slot yo.val) i = VG.Proof.X448.Radix16.decoded s.mem q i := fun i hi => by
    rw [m5.limbs s1y (by omega) hi, m4.limbs (by omega) (by omega) hi, l3 i hi]
  have by5 : Bounded s5.mem base (slot yo.val) := fun i hi => by rw [l5 i hi]; exact decoded_lt _ _ _
  refine WP.mono (VG.Proof.Ed448.X86.diffSlot_ok hs5 (by omega) b5 by5) fun t ⟨tb, tm, tk⟩ => ?_
  have fe5 : VG.Proof.X448.X86.fe s5.mem base VG.Impl.X448.X86.X2 = VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.decoded s.mem q) 28 % Spec.X448.P := by
    rw [v5]; exact congrArg (· % Spec.X448.P) ((VG.Proof.X448.Radix16.valN_congr f4).trans (VG.Proof.X448.Radix16.valN_congr l3))
  have fy5 : VG.Proof.X448.X86.fe s5.mem base (slot yo.val) = VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.decoded s.mem q) 28 := VG.Proof.X448.Radix16.valN_congr l5
  have tl : ∀ dd, 64 ≤ dd → dd + 112 ≤ 2880 → ∀ j < 28, limbs t.mem base dd j = limbs s5.mem base dd j :=
    fun dd h1 h2 j hj => tm.limbs (Or.inr (by simp only [BAD]; omega)) (by omega) hj
  have other : ∀ i : Index, i ≠ 1 → i ≠ yo → ∀ j < 28,
      limbs t.mem base (slot i.val) j = limbs s.mem base (slot i.val) j := by
    intro i hi1 hiy j hj
    have si := VG.Proof.Ed448.X86.slot_range i
    have s1i : slot i.val + 112 ≤ VG.Impl.X448.X86.X2 ∨ VG.Impl.X448.X86.X2 + 112 ≤ slot i.val := by rw [hX2]; exact slot_sep hi1
    have syi := slot_sep hiy
    rw [tl _ si.1 si.2 j hj, m5.limbs s1i (by omega) hj, m4.limbs (by omega) (by omega) hj,
      m3.limbs (Or.inr (by simp only [BAD]; omega)) (by omega) hj,
      o2.limbs (Or.inr (by simp only [SIGN]; omega)) (by omega) hj, m1.limbs (by omega) (by omega) hj]
  have bad3 : VG.Proof.X448.X86.word s5.mem base BAD = VG.Proof.X448.X86.word s3.mem base BAD := by
    rw [m5.word (Or.inl (by simp only [BAD]; omega)) (by simp only [BAD, ACC]; omega),
      m4.word (Or.inl (by simp only [BAD]; omega)) (by decide)]
  have bad2 : VG.Proof.X448.X86.word s2.mem base BAD = VG.Proof.X448.X86.word s.mem base BAD := by
    rw [o2.word (Or.inl (by decide)) (by decide), m1.word (Or.inl (by simp only [BAD]; omega)) (by decide)]
  refine ⟨⟨?_, ?_⟩, fun i j hj => ?_, ?_, ?_, ?_, fun i h1 hy => ?_⟩
  · refine (h0.rest (rs := .esi :: workRegs) (by decide)).trans (((k1.mono ?_).trans ((k2.mono ?_).trans ((k3.mono ?_).trans
      ((k4.mono ?_).trans (k5.mono ?_))))).trans (tk.mono ?_)) <;> intro r hr <;> revert r <;> decide
  · exact (((((VG.Proof.Ed448.X86.outV m1 (by omega) (by omega)).trans (VG.Proof.Ed448.X86.outV o2 (by decide) (by decide))).trans
      (VG.Proof.Ed448.X86.outV m3 (by decide) (by decide))).trans (VG.Proof.Ed448.X86.outV m4 (by decide) (by decide))).trans
      (VG.Proof.Ed448.X86.fmV m5 (by decide) (by decide))).trans (VG.Proof.Ed448.X86.outV tm (by decide) (by decide))
  · have si := VG.Proof.Ed448.X86.slot_range i
    rw [tl _ si.1 si.2 j hj]
    by_cases h1 : i = 1
    · subst i; exact b5 j hj
    · by_cases hy : i = yo
      · subst i; exact by5 j hj
      · rw [← tl _ si.1 si.2 j hj, other i h1 hy j hj]; exact hb i j hj
  · rw [tm.word (Or.inr (by decide)) (by decide), m5.word (Or.inl (by simp only [SIGN]; omega)) (by decide),
      m4.word (Or.inl (by simp only [SIGN]; omega)) (by decide),
      m3.word (Or.inr (by decide)) (by decide), m2]
    exact Mem.readW_writeW_self32 _ _ _
  · rw [bad3] at tb
    rw [bad2] at b3
    have h := b3.trans tb
    refine h.congr (and_congr_right fun _ => ?_)
    rw [VG.Proof.Ed448.X86.limbs_eq_iff b5 by5, fe5, fy5]
    exact Nat.mod_eq_iff_lt (NeZero.ne Spec.X448.P)
  · simp only [VG.Proof.X448.X86.E, VG.Proof.X448.X86.F]
    rw [show VG.Proof.X448.X86.fe t.mem base (slot yo.val) = VG.Proof.X448.X86.fe s5.mem base (slot yo.val) from VG.Proof.X448.Radix16.valN_congr (tl _ sy.1 sy.2),
      fy5]
  · simp only [VG.Proof.X448.X86.E, VG.Proof.X448.X86.F]
    exact congrArg Proof.X448.toFe (VG.Proof.X448.Radix16.valN_congr (other i h1 hy))

end VG.Proof.Ed448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.VerifySign`. -/
section

/-!
# Ed448 verification's equation on x86 (32-bit): the sign of a decoded point

`decodeSign_ok`: with the candidate `x` in slot `xo` and `-x` in slot 12,
`x` fully reduced in slot 1; `BAD |= 0` exactly when `x ≠ 0` or the sign bit
(`SIGN`) is 0; and `x` swapped with `-x` under the mask of its low bit
differing from the sign bit (RFC 8032 §5.2.3, step 4).
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Impl.Ed448.X86 VG.Proof.X448.X86 VG.Proof.X448.Radix16
open VG.Impl.X448.X86 (slot X2 ACC TMP ld st copy freeze cswap sc)

/-- `edx = ⋁` the limbs of slot 1: 0 exactly when they all are. -/
theorem orLimbs_ok {s : State} {base : Addr} (hs : Scr s base) (hb : Bounded s.mem base X2) :
    WP isa (.block orLimbs) s fun t =>
      (t.gpr .edx).toNat < 65536 ∧ (t.gpr .edx = 0 ↔ ∀ i < 28, limbs s.mem base X2 i = 0) ∧
        t.mem = s.mem ∧ Keeps [.edx] s t := by
  unfold orLimbs
  refine load_ok hs (by decide) fun u hu => ?_
  let inv := fun n (t : State) =>
    (t.gpr .edx).toNat < 65536 ∧ (t.gpr .edx = 0 ↔ ∀ i < n + 1, limbs s.mem base X2 i = 0) ∧
      t.mem = s.mem ∧ Keeps [.edx] s t
  have h0 : inv 0 u := by
    refine ⟨?_, ?_, hu.mem, hu.rest (by simp)⟩
    · rw [hu.gpr]; exact hb 0 (by decide)
    · rw [hu.gpr]
      exact ⟨fun h i hi => by rw [show i = 0 by omega]; exact congrArg BitVec.toNat h,
        fun h => BitVec.eq_of_toNat_eq (h 0 (by decide))⟩
  refine wp_range_flatMap (M := isa) (N := 27) inv (fun n t hn ⟨tb, tz, tm, tk⟩ => ?_) 27 (by decide) u h0
  have ht := hs.of_keeps tk (by decide)
  refine wp_alu (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (VG.Proof.Ed448.X86.rd_sc ht (by simp only [X2, slot]; omega))
    fun w hw _ => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · rw [hw.gpr]; change (t.gpr .edx ||| word t.mem base (X2 + 4 * (n + 1))).toNat < _
    rw [BitVec.toNat_or, tm]
    exact Nat.or_lt_two_pow (n := 16) tb (hb (n + 1) (by omega))
  · rw [hw.gpr]; change t.gpr .edx ||| word t.mem base (X2 + 4 * (n + 1)) = 0 ↔ _
    rw [tm]
    refine BitVec.or_eq_zero_iff.trans ((and_congr_left fun _ => tz).trans ?_)
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h1 i hi
      · exact congrArg BitVec.toNat h2
    · intro h
      exact ⟨fun i hi => h i (by omega), BitVec.eq_of_toNat_eq (h (n + 1) (by omega))⟩
  · rw [hw.mem, tm]
  · exact tk.trans (hw.rest (by simp))

theorem isZero16 (x : BitVec 32) (h : x.toNat < 65536) :
    (x - 1) >>> 31 = if x = 0 then 1 else 0 := by
  by_cases hx : x = 0
  · subst hx; decide
  · rw [ite_eq_right hx]
    have hx' : x.toNat ≠ 0 := fun e => hx (BitVec.eq_of_toNat_eq e)
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]
    change (2 ^ 32 - 1 + x.toNat) % 2 ^ 32 / 2 ^ 31 = 0
    omega

theorem zeroSign : ∀ z : Bool, ∀ sb < 2,
    (((if z then 1 else 0 : BitVec 32) &&& BitVec.ofNat 32 sb) = 0 ↔ ¬(z = true ∧ sb = 1)) ∧
      ((if z then 1 else 0 : BitVec 32) &&& BitVec.ofNat 32 sb).toNat < 65536 := by decide

theorem negMask : ∀ a < 2, ∀ sb < 2,
    (0 : BitVec 32) - (BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 sb) = VG.Proof.X448.X86.mask (decide (a ≠ sb)) := by decide

theorem and1 (w : BitVec 32) : w &&& 1 = BitVec.ofNat 32 (w.toNat % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (1 : BitVec 32).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := w.toNat % 2) (by omega)]

/-- After the `x = 0` check (`edx`, 0 exactly when `Z`): `BAD |= 0` exactly
when not both `Z` and the sign bit, and `ebx` the mask of the low bit `l₀`
differing from it. -/
theorem signTail_ok {s : State} {base : Addr} (hs : Scr s base) {Z : Prop} (h2 : (s.gpr .edx).toNat < 65536)
    (hz : s.gpr .edx = 0 ↔ Z) {sb : Nat} (hsb : sb < 2) (hsign : VG.Proof.X448.X86.word s.mem base SIGN = BitVec.ofNat 32 sb) :
    WP isa (.block (([.alu .sub .edx (.imm 1), .shift .shr .edx 31, .alu .and .edx (.mem (sc SIGN))] :
      List Instr) ++ orBad .edx ++ ([ld .eax X2, .alu .and .eax (.imm 1), .alu .xor .eax (.mem (sc SIGN)),
      .mov .ebx (.imm 0), .alu .sub .ebx (.reg .eax)] : List Instr))) s fun t =>
      VG.Proof.Ed448.X86.BadUpd (¬(Z ∧ sb = 1)) (VG.Proof.X448.X86.word s.mem base BAD) (VG.Proof.X448.X86.word t.mem base BAD) ∧
        t.gpr .ebx = VG.Proof.X448.X86.mask (decide (limbs s.mem base X2 0 % 2 ≠ sb)) ∧ Outside base BAD 4 s.mem t.mem ∧
        Keeps [.eax, .ebx, .edx] s t := by
  simp only [List.cons_append, List.nil_append]
  refine wp_alu (Or.inr (Or.inl rfl)) rfl fun u1 v1 _ => ?_
  refine wp_shift (by decide) fun u2 v2 => ?_
  have s2 := (hs.of_upd v1 (by decide)).of_upd v2 (by decide)
  refine wp_alu (Or.inr (Or.inr (Or.inl rfl))) (VG.Proof.Ed448.X86.rd_sc s2 (by decide)) fun u3 v3 _ => ?_
  have s3 := s2.of_upd v3 (by decide)
  have e3 : u3.gpr .edx = (if s.gpr .edx = 0 then 1 else 0 : BitVec 32) &&& BitVec.ofNat 32 sb := by
    rw [v3.gpr]; change u2.gpr .edx &&& VG.Proof.X448.X86.word u2.mem base SIGN = _
    rw [v2.gpr, v2.mem, v1.mem, hsign, v1.gpr]
    exact congrArg (· &&& _) (VG.Proof.Ed448.X86.isZero16 _ h2)
  have z := VG.Proof.Ed448.X86.zeroSign (decide (s.gpr .edx = 0)) sb hsb
  simp only [decide_eq_true_eq] at z
  rw [← e3] at z
  change WP isa (.block (orBad .edx ++ [ld .eax X2, .alu .and .eax (.imm 1), .alu .xor .eax (.mem (sc SIGN)),
    .mov .ebx (.imm 0), .alu .sub .ebx (.reg .eax)])) u3 _
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86.orBad_ok s3 (by decide) (P := ¬(Z ∧ sb = 1)) z.2 (z.1.trans (by rw [hz]))) fun u4 ⟨b4, o4, k4⟩ => ?_
  have s4 := s3.of_keeps k4 (by decide)
  refine load_ok s4 (by decide) fun u5 v5 => ?_
  have s5 := s4.of_upd v5 (by decide)
  refine wp_alu (Or.inr (Or.inr (Or.inl rfl))) rfl fun u6 v6 _ => ?_
  have s6 := s5.of_upd v6 (by decide)
  refine wp_alu (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) (VG.Proof.Ed448.X86.rd_sc s6 (by decide)) fun u7 v7 _ => ?_
  refine wp_mov rfl fun u8 v8 => ?_
  refine wp_alu (Or.inr (Or.inl rfl)) rfl fun t vt _ => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · have m3 : u3.mem = s.mem := by rw [v3.mem, v2.mem, v1.mem]
    have e : VG.Proof.X448.X86.word t.mem base BAD = VG.Proof.X448.X86.word u4.mem base BAD := by
      rw [vt.mem, v8.mem, v7.mem, v6.mem, v5.mem]
    rw [e, ← m3]
    exact b4
  · rw [vt.gpr]; change u8.gpr .ebx - u8.gpr .eax = _
    rw [v8.gpr, v8.other _ (by decide), v7.gpr]
    change (0 : BitVec 32) - (u6.gpr .eax ^^^ VG.Proof.X448.X86.word u6.mem base SIGN) = _
    rw [v6.gpr]
    change (0 : BitVec 32) - ((u5.gpr .eax &&& 1) ^^^ VG.Proof.X448.X86.word u6.mem base SIGN) = _
    rw [v5.gpr, v6.mem, v5.mem, VG.Proof.Ed448.X86.and1]
    have sg : VG.Proof.X448.X86.word u4.mem base SIGN = BitVec.ofNat 32 sb := by
      rw [o4.word (Or.inr (by decide)) (by decide), v3.mem, v2.mem, v1.mem, hsign]
    have l0 : (VG.Proof.X448.X86.word u4.mem base X2).toNat = limbs s.mem base X2 0 := by
      rw [o4.word (Or.inr (by decide)) (by decide), v3.mem, v2.mem, v1.mem]; rfl
    rw [sg, l0]
    exact VG.Proof.Ed448.X86.negMask _ (Nat.mod_lt _ (by decide)) sb hsb
  · intro x hx
    rw [vt.mem, v8.mem, v7.mem, v6.mem, v5.mem, o4 x hx, v3.mem, v2.mem, v1.mem]
  · exact (v1.rest (by simp)).trans ((v2.rest (by simp)).trans ((v3.rest (by simp)).trans
      ((k4.mono (by simp)).trans ((v5.rest (by simp)).trans ((v6.rest (by simp)).trans
      ((v7.rest (by simp)).trans ((v8.rest (by simp)).trans (vt.rest (by simp)))))))))

theorem sel_sign : ∀ a < 2, ∀ sb < 2, decide (a ≠ sb) = !((a == 1) == (sb == 1)) := by decide

theorem fe_zero_iff {m : Mem} {base : Addr} {o : Nat} (hb : Bounded m base o) :
    (∀ i < 28, limbs m base o i = 0) ↔ fe m base o = 0 := by
  have z : VG.Proof.X448.Radix16.valN (fun _ => 0) 28 = 0 := valN_zero 28
  constructor
  · intro h; exact (VG.Proof.X448.Radix16.valN_congr h).trans z
  · intro h; exact VG.Proof.Ed448.X86.valN_inj hb (fun _ _ => by decide) (h.trans z.symm)

/-- `decodeSign xo`, with `-x` in slot 12 and the sign bit `sb` at `SIGN`. -/
theorem decodeSign_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    (xo : Index) (hxo : xo = 6 ∨ xo = 8) {sb : Nat} (hsb : sb < 2)
    (hsign : VG.Proof.X448.X86.word s.mem base SIGN = BitVec.ofNat 32 sb)
    (hneg : E s.mem base 12 = (E s.mem base xo - E s.mem base xo) - E s.mem base xo) :
    WP isa (.block (decodeSign xo.val)) s fun t =>
      VG.Proof.Ed448.X86.CKeep base s t ∧ BoundedEnv t.mem base ∧
      VG.Proof.Ed448.X86.BadUpd (¬(E s.mem base xo = 0 ∧ sb = 1)) (VG.Proof.X448.X86.word s.mem base BAD) (VG.Proof.X448.X86.word t.mem base BAD) ∧
      E t.mem base xo = (if ((E s.mem base xo).val % 2 == 1) == (sb == 1) then E s.mem base xo
        else (E s.mem base xo - E s.mem base xo) - E s.mem base xo) ∧
      (∀ i : Index, i ≠ 1 → i ≠ 12 → i ≠ xo → E t.mem base i = E s.mem base i) := by
  have hx1 : xo ≠ 1 := by rcases hxo with rfl | rfl <;> decide
  have hx12 : xo ≠ 12 := by rcases hxo with rfl | rfl <;> decide
  have sx := VG.Proof.Ed448.X86.slot_range xo
  have hX2v : X2 = 192 := rfl
  have hA : ACC = 3584 := rfl
  have hX2 : X2 = slot (1 : Index).val := rfl
  have s1x : slot xo.val + 112 ≤ X2 ∨ X2 + 112 ≤ slot xo.val := by rw [hX2]; exact slot_sep hx1
  unfold decodeSign
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.copy_ok hs (o := X2) (a := slot xo.val) (by decide) (by omega)
    (Or.inr (by omega))) fun s1 ⟨f1, m1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  have bd1 : Bounded s1.mem base X2 := fun i hi => by rw [f1 i hi]; exact hb xo i hi
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.freeze_ok hs1 bd1) fun s2 ⟨b2, v2, m2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86.orLimbs_ok hs2 b2) fun s3 ⟨r3b, r3z, m3, k3⟩ => ?_
  have hs3 := hs2.of_keeps k3 (by decide)
  have fx : fe s2.mem base X2 = (E s.mem base xo).val := by
    rw [v2, show fe s1.mem base X2 = fe s.mem base (slot xo.val) from VG.Proof.X448.Radix16.valN_congr f1]; rfl
  have zero : (∀ i < 28, limbs s2.mem base X2 i = 0) ↔ E s.mem base xo = 0 := by
    rw [VG.Proof.Ed448.X86.fe_zero_iff b2, fx]; exact Fin.val_eq_zero_iff
  have sign3 : VG.Proof.X448.X86.word s3.mem base SIGN = BitVec.ofNat 32 sb := by
    rw [m3, m2.word (Or.inl (by simp only [SIGN]; omega)) (by decide),
      m1.word (Or.inl (by simp only [SIGN]; omega)) (by decide), hsign]
  rw [zero] at r3z
  rw [← List.append_assoc, ← List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86.signTail_ok hs3 r3b r3z hsb sign3) fun s4 ⟨b4, c4, m4, k4⟩ => ?_
  have hs4 := hs3.of_keeps k4 (by decide)
  have e4 : ∀ i : Index, i ≠ 1 → ∀ j < 28, limbs s4.mem base (slot i.val) j = limbs s.mem base (slot i.val) j := by
    intro i h1 j hj
    have si := VG.Proof.Ed448.X86.slot_range i
    have s1i : slot i.val + 112 ≤ X2 ∨ X2 + 112 ≤ slot i.val := by rw [hX2]; exact slot_sep h1
    rw [m4.limbs (Or.inr (by simp only [BAD]; omega)) (by omega) hj, m3, m2.limbs s1i (by omega) hj,
      m1.limbs (by omega) (by omega) hj]
  have bd4 : BoundedEnv s4.mem base := by
    intro i j hj
    by_cases h1 : i = 1
    · subst i
      rw [m4.limbs (Or.inr (by simp only [BAD, slot]; omega)) (by decide) hj, m3]; exact b2 j hj
    · rw [e4 i h1 j hj]; exact hb i j hj
  refine WP.mono (cswapE hs4 bd4 xo 12 hx12 c4) fun t ⟨kt, bt, _, et⟩ => ?_
  have E4 : ∀ i : Index, i ≠ 1 → E s4.mem base i = E s.mem base i := fun i h1 => by
    simp only [E, VG.Proof.X448.X86.F]; exact congrArg Proof.X448.toFe (VG.Proof.X448.Radix16.valN_congr (e4 i h1))
  have l0 : limbs s3.mem base X2 0 % 2 = (E s.mem base xo).val % 2 := by
    rw [m3, ← fe_mod2, fx]
  have bad3 : VG.Proof.X448.X86.word s3.mem base BAD = VG.Proof.X448.X86.word s.mem base BAD := by
    rw [m3, m2.word (Or.inl (by simp only [BAD]; omega)) (by simp only [BAD, ACC]; omega),
      m1.word (Or.inl (by simp only [BAD]; omega)) (by decide)]
  refine ⟨⟨?_, ?_⟩, bt, ?_, ?_, fun i h1 h12 hx => ?_⟩
  · refine (((k1.mono ?_).trans ((k2.mono ?_).trans ((k3.mono ?_).trans (k4.mono ?_)))).trans
      (kt.regs.mono ?_)) <;> intro r hr <;> revert r <;> decide
  · exact (((VG.Proof.Ed448.X86.outB m1 (by decide) (by decide)).trans (VG.Proof.Ed448.X86.fmB m2 (by decide) (by decide))).trans
      (by rw [← m3]; exact (BMem.of_bad m4))).trans (BMem.of_outside2 kt.mem)
  · rw [kt.mem.word (Or.inl (by decide)) (Or.inl (by decide)) (by decide), ← bad3]
    exact b4
  · rw [et]
    simp only [opSwap, Function.update_of_ne hx12, Function.update_self]
    rw [E4 xo hx1, E4 12 (by decide), hneg, l0, VG.Proof.Ed448.X86.sel_sign _ (Nat.mod_lt _ (by decide)) sb hsb]
    cases ((E s.mem base xo).val % 2 == 1) == (sb == 1) <;> rfl
  · rw [et]
    simp only [opSwap, Function.update_of_ne h12, Function.update_of_ne hx]
    exact E4 i h1

end VG.Proof.Ed448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.VerifyRoot`. -/
section

/-!
# Ed448 verification's equation on x86 (32-bit): the square root's power

`root`: X448's addition chain for the inversion as far as `z^(2^223 - 1)`,
then 223 squarings and a multiplication, for `z` in slot 12, into slot 21
with the temporaries 14–20: `Proof.Ed448.rootPow`, `z^((p-3)/4)`.
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Impl.Ed448.X86 VG.Proof.X448.X86

/-- The field slots after `root`. -/
def rootEnv (e : Env) : Env :=
  let e := applyOps [.copy 14 12] e
  let e := opSqn 14 1 e
  let e := applyOps [.mul 14 14 12, .copy 15 14] e
  let e := opSqn 15 2 e
  let e := applyOps [.mul 15 15 14, .copy 16 15] e
  let e := opSqn 16 4 e
  let e := applyOps [.mul 16 16 15, .copy 17 16] e
  let e := opSqn 17 8 e
  let e := applyOps [.mul 17 17 16, .copy 18 17] e
  let e := opSqn 18 16 e
  let e := applyOps [.mul 18 18 17, .copy 19 18] e
  let e := opSqn 19 32 e
  let e := applyOps [.mul 19 19 18, .copy 20 19] e
  let e := opSqn 20 64 e
  let e := applyOps [.mul 20 20 19] e
  let e := opSqn 20 64 e
  let e := applyOps [.mul 20 20 19] e
  let e := opSqn 20 16 e
  let e := applyOps [.mul 20 20 17] e
  let e := opSqn 20 8 e
  let e := applyOps [.mul 20 20 16] e
  let e := opSqn 20 4 e
  let e := applyOps [.mul 20 20 15] e
  let e := opSqn 20 2 e
  let e := applyOps [.mul 20 20 14, .copy 21 20] e
  let e := opSqn 21 1 e
  let e := applyOps [.mul 21 21 12] e
  let e := opSqn 21 223 e
  applyOps [.mul 21 21 20] e

theorem root_spec (base : Addr) : ISpec base root VG.Proof.Ed448.X86.rootEnv := by
  have h : ISpec base _ _ :=
    (opsI base [.copy 14 12]).seq <|
    (sqnI base 14 (n := 1) (by decide) (by decide)).seq <|
    (opsI base [.mul 14 14 12, .copy 15 14]).seq <|
    (sqnI base 15 (n := 2) (by decide) (by decide)).seq <|
    (opsI base [.mul 15 15 14, .copy 16 15]).seq <|
    (sqnI base 16 (n := 4) (by decide) (by decide)).seq <|
    (opsI base [.mul 16 16 15, .copy 17 16]).seq <|
    (sqnI base 17 (n := 8) (by decide) (by decide)).seq <|
    (opsI base [.mul 17 17 16, .copy 18 17]).seq <|
    (sqnI base 18 (n := 16) (by decide) (by decide)).seq <|
    (opsI base [.mul 18 18 17, .copy 19 18]).seq <|
    (sqnI base 19 (n := 32) (by decide) (by decide)).seq <|
    (opsI base [.mul 19 19 18, .copy 20 19]).seq <|
    (sqnI base 20 (n := 64) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 19]).seq <|
    (sqnI base 20 (n := 64) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 19]).seq <|
    (sqnI base 20 (n := 16) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 17]).seq <|
    (sqnI base 20 (n := 8) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 16]).seq <|
    (sqnI base 20 (n := 4) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 15]).seq <|
    (sqnI base 20 (n := 2) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 14, .copy 21 20]).seq <|
    (sqnI base 21 (n := 1) (by decide) (by decide)).seq <|
    (opsI base [.mul 21 21 12]).seq <|
    (sqnI base 21 (n := 223) (by decide) (by decide)).seq <|
    (opsI base [.mul 21 21 20])
  exact h

theorem rootEnv_eval (e : Env) : VG.Proof.Ed448.X86.rootEnv e 21 = Proof.Ed448.rootPow (e 12) := by
  simp only [↓reduceIte, VG.Proof.Ed448.X86.rootEnv, applyOps, FieldOp.apply, opMul, opCopy, opSqn,
    Function.update_apply]
  rfl

theorem rootEnv_keep (e : Env) (i : Index) (hi : i.val < 14) : VG.Proof.Ed448.X86.rootEnv e i = e i := by
  have h14 : i ≠ 14 := fun h => by subst h; omega
  have h15 : i ≠ 15 := fun h => by subst h; omega
  have h16 : i ≠ 16 := fun h => by subst h; omega
  have h17 : i ≠ 17 := fun h => by subst h; omega
  have h18 : i ≠ 18 := fun h => by subst h; omega
  have h19 : i ≠ 19 := fun h => by subst h; omega
  have h20 : i ≠ 20 := fun h => by subst h; omega
  have h21 : i ≠ 21 := fun h => by subst h; omega
  simp only [VG.Proof.Ed448.X86.rootEnv, applyOps, FieldOp.apply, opMul, opCopy, opSqn,
    Function.update_of_ne h21, Function.update_of_ne h14, Function.update_of_ne h15,
    Function.update_of_ne h16, Function.update_of_ne h17, Function.update_of_ne h18,
    Function.update_of_ne h19, Function.update_of_ne h20]

theorem root_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) :
    WP isa root s fun t =>
      IKeep base s t ∧ BoundedEnv t.mem base ∧ VG.Proof.X448.X86.E t.mem base = VG.Proof.Ed448.X86.rootEnv (VG.Proof.X448.X86.E s.mem base) :=
  VG.Proof.Ed448.X86.root_spec base s hs hb

end VG.Proof.Ed448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.VerifyDecode`. -/
section

/-!
# Ed448 verification's equation on x86 (32-bit): decoding a point

`decode_ok`: `decode d xo yo` on the 57 bytes at `q`, the argument at
`[esp + d]` (RFC 8032 §5.2.3): `BAD |= 0` exactly when they decode, and then
the point is `(x : y : 1)` with `x` in slot `xo` and `y` in slot `yo` (by
`Proof.Ed448.decodePoint_impl`, given `RecoverOk`). The steps' field values
(`Proof/Ed448/VerifyFormulas.lean`): `u = y² - 1`, `v = d y² - 1`, `t = u³v`,
`x = t (t (uv)²)^((p-3)/4)`, the check `v x² = u`, and the sign.
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Impl.Ed448 VG.Impl.Ed448.X86 VG.Proof.X448.X86 VG.Proof.X448.Radix16
open VG.Impl.X448.X86 (slot X2 ACC at_)
open VG.Proof.Ed448 (RecoverOk rootPow evalOps fopValid)

/-! ## The bytes -/

theorem bytesAt57_take (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 57).take 56 = Spec.Ed448.bytesAt m p 56 := by
  simp [Spec.Ed448.bytesAt, ← List.map_take, List.take_range]

theorem bytesAt57_getD (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 57).getD 56 0 = m (p + BitVec.ofNat 64 56) := by
  simp [Spec.Ed448.bytesAt, List.getD_eq_getElem?_getD]

theorem bytesAt57_len (m : Mem) (p : Addr) : (Spec.Ed448.bytesAt m p 57).length = 57 := by
  simp [Spec.Ed448.bytesAt]

theorem decodeLE_56 (m : Mem) (p : Addr) :
    Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m p 56) = VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.decoded m p) 28 := by
  rw [Proof.Ed448.decodeLE_eq, show (56 : Nat) = 2 * 28 from rfl]
  exact VG.Proof.X448.Radix16.decoded_val m p 28

/-! ## Decoding -/

theorem decode_ok (hR : RecoverOk) {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    {d : Nat} {a : Addr} (ha : s.ea (at_ .esp d) = a) (har : InRegions (s.rd ++ s.wr) a 4)
    {p : BitVec 32} (hp : s.mem.readW a 32 = p) (hfit : p.toNat + 57 ≤ 2 ^ 32)
    (hr : ∀ j < 57, InRegions (s.rd ++ s.wr) (p.setWidth 64 + BitVec.ofNat 64 j) 1)
    (hd : ∀ j < 57, 8192 ≤ ofs base (p.setWidth 64 + BitVec.ofNat 64 j))
    (xo yo : Index) (hxy : xo = 6 ∧ yo = 7 ∨ xo = 8 ∧ yo = 9)
    (h10 : E s.mem base 10 = 1) (h11 : E s.mem base 11 = Spec.Ed448.d) :
    WP isa (decode d xo.val yo.val) s fun t =>
      VG.Proof.Ed448.X86.VKeep base s t ∧ BoundedEnv t.mem base ∧
      VG.Proof.Ed448.X86.BadUpd ((Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (p.setWidth 64) 57)).isSome)
        (VG.Proof.X448.X86.word s.mem base BAD) (VG.Proof.X448.X86.word t.mem base BAD) ∧
      (∀ a, Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (p.setWidth 64) 57) = some a →
        E t.mem base xo = a.X ∧ E t.mem base yo = a.Y ∧ a.Z = 1) ∧
      (∀ i : Index, i ≠ xo → i ≠ yo → (i.val = 0 ∨ i.val = 2 ∨ (6 ≤ i.val ∧ i.val ≤ 11)) →
        E t.mem base i = E s.mem base i) := by
  have hxo : xo = 6 ∨ xo = 8 := by rcases hxy with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  have hyx : yo ≠ xo := by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hy1 : yo ≠ 1 := by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
  have hx1 : xo ≠ 1 := by rcases hxo with rfl | rfl <;> decide
  have hx12 : xo ≠ 12 := by rcases hxo with rfl | rfl <;> decide
  have hxlt : xo.val < 14 := by rcases hxo with rfl | rfl <;> decide
  have hylt : yo.val < 14 := by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
  generalize hq : p.setWidth 64 = q
  unfold decode
  -- `y`, the sign bit, and the first checks
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86.decodeY_ok hs hb ha har hp hfit hr hd yo hy1)
    fun s1 ⟨k1, b1, sg1, c1, y1, e1⟩ => ?_)
  rw [hq] at sg1 c1 y1
  have hs1 := k1.scr hs
  -- `u`, `v`, `t` and `t (uv)²`
  refine VG.Proof.Ed448.X86.field_seq (decodeUV yo.val xo.val)
    (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) hs1 b1 fun s2 k2 b2 e2 => ?_
  have hs2 := k2.scr hs1
  -- the root
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86.root_ok hs2 b2) fun s3 ⟨k3, b3, e3⟩ => ?_)
  have hs3 := k3.scr hs2
  -- `x` and `v x²`
  refine VG.Proof.Ed448.X86.field_seq [.mul xo.val xo.val 21, .sqr 12 xo.val, .mul 12 3 12]
    (by rcases hxo with rfl | rfl <;> decide) hs3 b3 fun s4 k4 b4 e4 => ?_
  have hs4 := k4.scr hs3
  -- `v x² = u`
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86.eqSlots_ok hs4 b4 12 13 (by decide) (by decide) (by decide))
    fun s5 ⟨k5, b5, e5, c5⟩ => ?_)
  have hs5 := k5.scr hs4
  -- `-x`
  refine VG.Proof.Ed448.X86.field_seq [.sub 12 xo.val xo.val, .sub 12 12 xo.val]
    (by rcases hxo with rfl | rfl <;> decide) hs5 b5 fun s6 k6 b6 e6 => ?_
  have hs6 := k6.scr hs5
  -- the sign
  have hb128 : (s.mem (q + BitVec.ofNat 64 56)).toNat / 128 < 2 := by
    have := (s.mem (q + BitVec.ofNat 64 56)).isLt; omega
  have K16 : VG.Proof.Ed448.X86.CKeep base s1 s6 :=
    (Keep.toC k2).trans ((IKeep.toC k3).trans ((Keep.toC k4).trans (k5.trans (Keep.toC k6))))
  have sg : VG.Proof.X448.X86.word s6.mem base SIGN = BitVec.ofNat 32 ((s.mem (q + BitVec.ofNat 64 56)).toNat / 128) := by
    rw [K16.sign, sg1]
  -- the values
  have h10' : E s1.mem base 10 = 1 := by
    rw [e1 10 (by decide) (by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide), h10]
  have h11' : E s1.mem base 11 = Spec.Ed448.d := by
    rw [e1 11 (by decide) (by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide), h11]
  obtain ⟨u2, v2, t2, w2, k2e⟩ := Proof.Ed448.decodeUV_eval xo yo hxy (E s1.mem base)
  simp only [h10', h11', y1, ← e2] at u2 v2 t2 w2 k2e
  generalize hY : Proof.X448.toFe (VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.decoded s.mem q) 28) = Y at *
  generalize hu : Y * Y - 1 = u at *
  generalize hv : Spec.Ed448.d * (Y * Y) - 1 = v at *
  generalize ht : u * u * u * v = tt at *
  have r321 : E s3.mem base 21 = rootPow (E s2.mem base 12) := by rw [e3, VG.Proof.Ed448.X86.rootEnv_eval]
  have r3k : ∀ i : Index, i.val < 14 → E s3.mem base i = E s2.mem base i :=
    fun i h => by rw [e3, VG.Proof.Ed448.X86.rootEnv_keep _ _ h]
  obtain ⟨x4, w4, u4, k4e⟩ := Proof.Ed448.decodeXOps_eval xo hxo (E s3.mem base)
  rw [← e4] at k4e
  rw [← e4, r3k xo hxlt, t2, r321, w2] at x4
  rw [← e4, r3k 3 (by decide), v2, r3k xo hxlt, t2, r321, w2] at w4
  rw [← e4, r3k 13 (by decide), u2] at u4
  generalize hx : tt * rootPow (tt * ((u * v) * (u * v))) = x at *
  have x5 : E s5.mem base xo = x := by rw [e5 xo hx1, x4]
  obtain ⟨n6, k6e⟩ := Proof.Ed448.subNeg_eval xo hx12 (E s5.mem base)
  rw [← e6] at n6 k6e
  have x6 : E s6.mem base xo = x := by rw [k6e xo hx12, x5]
  rw [x5] at n6
  refine WP.mono (VG.Proof.Ed448.X86.decodeSign_ok hs6 b6 xo hxo hb128 sg (by rw [x6]; exact n6))
    fun t ⟨kt, bt, ct, xt, et⟩ => ?_
  rw [x6] at ct xt
  rw [w4, u4] at c5
  -- `decodePoint`
  have hD := Proof.Ed448.decodePoint_impl hR (Spec.Ed448.bytesAt s.mem q 57) (VG.Proof.Ed448.X86.bytesAt57_len _ _)
    (VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.decoded s.mem q) 28) ((s.mem (q + BitVec.ofNat 64 56)).toNat)
    (by rw [VG.Proof.Ed448.X86.bytesAt57_take, VG.Proof.Ed448.X86.decodeLE_56]) (by rw [VG.Proof.Ed448.X86.bytesAt57_getD]) Y u v tt x hY hu hv ht hx
  have kY : E t.mem base yo = Y := by
    rw [et yo hy1 (by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide) hyx,
      k6e yo (by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide), e5 yo hy1, k4e yo hyx
      (by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide), r3k yo hylt,
      k2e yo (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
        (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
        (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
        (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
        (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) hyx, y1]
  refine ⟨k1.trans ((Keep.toV k2).trans ((IKeep.toV k3).trans ((Keep.toV k4).trans
    ((CKeep.toV k5).trans ((Keep.toV k6).trans (CKeep.toV kt)))))), bt, ?_, fun a ha => ?_,
    fun i hix hiy hi => ?_⟩
  · have c5' : VG.Proof.Ed448.X86.BadUpd (v * (x * x) = u) (VG.Proof.X448.X86.word s1.mem base BAD) (VG.Proof.X448.X86.word s5.mem base BAD) := by
      rw [← Keep.bad k2, ← IKeep.bad k3, ← Keep.bad k4]; exact c5
    have ct' : VG.Proof.Ed448.X86.BadUpd (¬(x = 0 ∧ (s.mem (q + BitVec.ofNat 64 56)).toNat / 128 = 1)) (VG.Proof.X448.X86.word s5.mem base BAD)
        (VG.Proof.X448.X86.word t.mem base BAD) := by
      rw [← Keep.bad k6]; exact ct
    refine ((c1.trans c5').trans ct').congr ?_
    rw [hD]
    by_cases hall : ((s.mem (q + BitVec.ofNat 64 56)).toNat % 128 = 0 ∧
        VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.decoded s.mem q) 28 < Spec.X448.P) ∧ v * (x * x) = u ∧
        ¬ (x = 0 ∧ (s.mem (q + BitVec.ofNat 64 56)).toNat / 128 = 1)
    · rw [ite_eq_left hall]
      exact ⟨fun _ => rfl, fun _ => ⟨⟨hall.1, hall.2.1⟩, hall.2.2⟩⟩
    · rw [ite_eq_right hall]
      exact ⟨fun h => absurd ⟨h.1.1, h.1.2, h.2⟩ hall, fun h => absurd h (by simp)⟩
  · rw [hD] at ha
    by_cases hall : ((s.mem (q + BitVec.ofNat 64 56)).toNat % 128 = 0 ∧
        VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.decoded s.mem q) 28 < Spec.X448.P) ∧ v * (x * x) = u ∧
        ¬ (x = 0 ∧ (s.mem (q + BitVec.ofNat 64 56)).toNat / 128 = 1)
    · rw [ite_eq_left hall] at ha
      cases ha
      exact ⟨xt, kY, rfl⟩
    · rw [ite_eq_right hall] at ha
      cases ha
  · have h1 : i ≠ 1 := fun h => by subst h; omega
    have h12 : i ≠ 12 := fun h => by subst h; omega
    have h3 : i ≠ 3 := fun h => by subst h; omega
    have h4 : i ≠ 4 := fun h => by subst h; omega
    have h5 : i ≠ 5 := fun h => by subst h; omega
    have h13 : i ≠ 13 := fun h => by subst h; omega
    rw [et i h1 h12 hix, k6e i h12, e5 i h1, k4e i hix h12, r3k i (by omega),
      k2e i h3 h4 h5 h12 h13 hix, e1 i h1 hiy]

end VG.Proof.Ed448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.VerifyFinish`. -/
section

/-!
# Ed448 verification's equation on x86 (32-bit): the comparison and the result

`vfinish_ok`: `[4]Q` (`Q` in slots 0, 6 and 2) and `[4]R` (slots 8–10),
compared projectively (`X_Q Z_R = X_R Z_Q`, then `Y_Q Z_R = Y_R Z_Q`, each
check ORed into `BAD`), the callee-saved registers restored, and
`eax = (BAD == 0)`.
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Impl.Ed448 VG.Impl.Ed448.X86 VG.Proof.X448.X86
open VG.Proof.Ed448 (double evalOps evalOps_keep evalOps_append fopDest pt)
open VG.Impl.X448.X86 (slot ACC ld restore)

theorem doubleAt_keep062 (e : Env) (i : Index) (hi : 8 ≤ i.val ∧ i.val < 11) :
    evalOps (doubleAt 0 6 2) e i = e i :=
  evalOps_keep _ _ _ fun op hop => by
    have : ∀ op ∈ doubleAt 0 6 2, fopDest op = 0 ∨ fopDest op = 2 ∨ fopDest op = 6 ∨
        (12 ≤ fopDest op ∧ fopDest op < 20) := by decide
    have := this op hop
    omega

theorem doubleAt_eval062 (e : Env) :
    pt (evalOps (doubleAt 0 6 2) e) 0 6 2 = double (pt e 0 6 2) := rfl

/-- The doublings and the first products. -/
def vcompare : List FOp :=
  doubleAt 0 6 2 ++ doubleAt 0 6 2 ++ doubleAt 8 9 10 ++ doubleAt 8 9 10 ++ [.mul 12 0 10, .mul 13 8 2]

/-- `[4]Q` and `[4]R`, and the first products `X_Q Z_R` and `X_R Z_Q`. -/
theorem compare_eval (e : Env) :
    pt (evalOps VG.Proof.Ed448.X86.vcompare e) 0 6 2 = double (double (pt e 0 6 2)) ∧
    pt (evalOps VG.Proof.Ed448.X86.vcompare e) 8 9 10 = double (double (pt e 8 9 10)) ∧
    evalOps VG.Proof.Ed448.X86.vcompare e 12 = evalOps VG.Proof.Ed448.X86.vcompare e 0 * evalOps VG.Proof.Ed448.X86.vcompare e 10 ∧
    evalOps VG.Proof.Ed448.X86.vcompare e 13 = evalOps VG.Proof.Ed448.X86.vcompare e 8 * evalOps VG.Proof.Ed448.X86.vcompare e 2 := by
  have hk : ∀ (ec : Env) (i : Index), i.val < 11 →
      evalOps [.mul 12 0 10, .mul 13 8 2] ec i = ec i := fun ec i hi =>
    evalOps_keep _ _ _ fun op hop => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
      rcases hop with rfl | rfl <;> simp only [fopDest] <;> omega
  have p12 : ∀ ec : Env, evalOps [.mul 12 0 10, .mul 13 8 2] ec 12 = ec 0 * ec 10 := fun _ => rfl
  have p13 : ∀ ec : Env, evalOps [.mul 12 0 10, .mul 13 8 2] ec 13 = ec 8 * ec 2 := fun _ => rfl
  simp only [VG.Proof.Ed448.X86.vcompare, evalOps_append]
  generalize h1 : evalOps (doubleAt 0 6 2) e = e1
  generalize h2 : evalOps (doubleAt 0 6 2) e1 = e2
  generalize h3 : evalOps (doubleAt 8 9 10) e2 = e3
  generalize h4 : evalOps (doubleAt 8 9 10) e3 = e4
  have q4 : pt e4 0 6 2 = double (double (pt e 0 6 2)) := by
    rw [VG.Proof.Ed448.X86.pt_congr' (by rw [← h4, Proof.Ed448.doubleAt_keep8 _ _ (Or.inl (by decide))])
      (by rw [← h4, Proof.Ed448.doubleAt_keep8 _ _ (Or.inl (by decide))])
      (by rw [← h4, Proof.Ed448.doubleAt_keep8 _ _ (Or.inl (by decide))]),
      VG.Proof.Ed448.X86.pt_congr' (by rw [← h3, Proof.Ed448.doubleAt_keep8 _ _ (Or.inl (by decide))])
      (by rw [← h3, Proof.Ed448.doubleAt_keep8 _ _ (Or.inl (by decide))])
      (by rw [← h3, Proof.Ed448.doubleAt_keep8 _ _ (Or.inl (by decide))]),
      ← h2, VG.Proof.Ed448.X86.doubleAt_eval062, ← h1, VG.Proof.Ed448.X86.doubleAt_eval062]
  have r4 : pt e4 8 9 10 = double (double (pt e 8 9 10)) := by
    rw [← h4, Proof.Ed448.doubleAt_eval8, ← h3, Proof.Ed448.doubleAt_eval8,
      VG.Proof.Ed448.X86.pt_congr' (by rw [← h2, VG.Proof.Ed448.X86.doubleAt_keep062 _ _ (by decide)])
      (by rw [← h2, VG.Proof.Ed448.X86.doubleAt_keep062 _ _ (by decide)]) (by rw [← h2, VG.Proof.Ed448.X86.doubleAt_keep062 _ _ (by decide)]),
      VG.Proof.Ed448.X86.pt_congr' (by rw [← h1, VG.Proof.Ed448.X86.doubleAt_keep062 _ _ (by decide)])
      (by rw [← h1, VG.Proof.Ed448.X86.doubleAt_keep062 _ _ (by decide)]) (by rw [← h1, VG.Proof.Ed448.X86.doubleAt_keep062 _ _ (by decide)])]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [VG.Proof.Ed448.X86.pt_congr' (hk e4 0 (by decide)) (hk e4 6 (by decide)) (hk e4 2 (by decide)), q4]
  · rw [VG.Proof.Ed448.X86.pt_congr' (hk e4 8 (by decide)) (hk e4 9 (by decide)) (hk e4 10 (by decide)), r4]
  · rw [p12, hk e4 0 (by decide), hk e4 10 (by decide)]
  · rw [p13, hk e4 8 (by decide), hk e4 2 (by decide)]

/-- `ecx = (BAD == 0)`. -/
theorem isZeroBad_ok {s : State} {base : Addr} (hs : Scr s base) (h : (VG.Proof.X448.X86.word s.mem base BAD).toNat < 65536) :
    WP isa (.block ([ld .ecx BAD, .alu .sub .ecx (.imm 1), .shift .shr .ecx 31] : List Instr)) s fun t =>
      t.gpr .ecx = (if VG.Proof.X448.X86.word s.mem base BAD = 0 then 1 else 0) ∧ t.mem = s.mem ∧ Keeps [.ecx] s t := by
  refine load_ok hs (by decide) fun u hu => ?_
  refine wp_alu (Or.inr (Or.inl rfl)) rfl fun v hv _ => ?_
  refine wp_shift (by decide) fun t ht => WP.block_nil ⟨?_, by rw [ht.mem, hv.mem, hu.mem], ?_⟩
  · rw [ht.gpr, hv.gpr]
    change (u.gpr .ecx - 1) >>> 31 = _
    rw [hu.gpr]
    exact VG.Proof.Ed448.X86.isZero16 _ h
  · exact (hu.rest (by simp)).trans ((hv.rest (by simp)).trans (ht.rest (by simp)))

/-- The comparison and the result. -/
theorem vfinish_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    {g : Reg → BitVec 32} (hsv : VG.Proof.X448.X86.Saved base g s.mem) (h12 : (VG.Proof.X448.X86.word s.mem base BAD).toNat < 65536) :
    WP isa vfinish s fun t =>
      t.gpr .eax = (if VG.Proof.X448.X86.word s.mem base BAD = 0 ∧
        Spec.Ed448.pointEqual (double (double (pt (E s.mem base) 0 6 2)))
          (double (double (pt (E s.mem base) 8 9 10))) = true then 1 else 0) ∧
      (∀ p ∈ VG.Proof.X448.X86.savedSlots, t.gpr p.1 = g p.1) ∧ t.gpr .esp = s.gpr .esp ∧
      Outside base 0 8192 s.mem t.mem := by
  unfold vfinish
  refine VG.Proof.Ed448.X86.field_seq VG.Proof.Ed448.X86.vcompare (by decide) hs hb fun s1 k1 b1 e1 => ?_
  have hs1 := k1.scr hs
  obtain ⟨q1, r1, x12, x13⟩ := VG.Proof.Ed448.X86.compare_eval (E s.mem base)
  rw [← e1] at q1 r1 x12 x13
  rw [WP.seq_iff]
  refine WP.mono (VG.Proof.Ed448.X86.eqSlots_ok hs1 b1 12 13 (by decide) (by decide) (by decide))
    fun s2 ⟨k2, b2, e2, c2⟩ => ?_
  have hs2 := k2.scr hs1
  refine VG.Proof.Ed448.X86.field_seq [.mul 12 6 10, .mul 13 9 2] (by decide) hs2 b2 fun s3 k3 b3 e3 => ?_
  have hs3 := k3.scr hs2
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86.eqSlots_ok hs3 b3 12 13 (by decide) (by decide) (by decide))
    fun s4 ⟨k4, b4, e4, c4⟩ => ?_
  have hs4 := k4.scr hs3
  obtain ⟨c, hc, hcz, he⟩ := c2
  obtain ⟨c', hc', hcz', he'⟩ := c4
  have bad1 : VG.Proof.X448.X86.word s1.mem base BAD = VG.Proof.X448.X86.word s.mem base BAD := Keep.bad k1
  have bad3 : VG.Proof.X448.X86.word s3.mem base BAD = VG.Proof.X448.X86.word s2.mem base BAD := Keep.bad k3
  have hbad : VG.Proof.X448.X86.word s4.mem base BAD = VG.Proof.X448.X86.word s.mem base BAD ||| c ||| c' := by rw [he', bad3, he, bad1]
  have h4 : (VG.Proof.X448.X86.word s4.mem base BAD).toNat < 65536 := by
    rw [hbad, BitVec.toNat_or, BitVec.toNat_or]
    exact Nat.or_lt_two_pow (n := 16) (Nat.or_lt_two_pow (n := 16) h12 hc) hc'
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86.isZeroBad_ok hs4 h4) fun s5 ⟨v5, m5, k5⟩ => ?_
  have hs5 := hs4.of_keeps k5 (by decide)
  have sv5 : VG.Proof.X448.X86.Saved base g s5.mem := by
    rw [m5]
    exact (((hsv.outside2 k1.mem (by decide) (by decide)).outside2 k2.mem.widen (by decide)
      (by decide)).outside2 k3.mem (by decide) (by decide)).outside2 k4.mem.widen (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.restore_ok hs5 sv5) fun s6 ⟨r6, m6, k6⟩ => ?_
  refine wp_mov rfl fun t ht => WP.block_nil ⟨?_, fun p hp => ?_, ?_, ?_⟩
  · rw [ht.gpr]; change s6.gpr .ecx = _
    rw [k6.1 _ (by decide), v5, hbad]
    refine if_congr ?_ rfl rfl
    -- the values
    have y12 : E s3.mem base 12 = E s1.mem base 6 * E s1.mem base 10 := by
      rw [e3, ← e2 6 (by decide), ← e2 10 (by decide)]; rfl
    have y13 : E s3.mem base 13 = E s1.mem base 9 * E s1.mem base 2 := by
      rw [e3, ← e2 9 (by decide), ← e2 2 (by decide)]; rfl
    have hpe : Spec.Ed448.pointEqual (pt (E s1.mem base) 0 6 2) (pt (E s1.mem base) 8 9 10) = true ↔
        (E s1.mem base 0 * E s1.mem base 10 = E s1.mem base 8 * E s1.mem base 2 ∧
          E s1.mem base 6 * E s1.mem base 10 = E s1.mem base 9 * E s1.mem base 2) := by
      simp only [Spec.Ed448.pointEqual, pt, Bool.and_eq_true, beq_iff_eq]
    refine (BitVec.or_eq_zero_iff.trans (and_congr_left fun _ => BitVec.or_eq_zero_iff)).trans ?_
    refine (and_congr (and_congr Iff.rfl hcz) hcz').trans ?_
    rw [y12, y13, x12, x13, ← q1, ← r1, hpe]
    exact and_assoc
  · have hne : p.1 ≠ .eax := by
      simp only [VG.Proof.X448.X86.savedSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> decide
    rw [ht.other _ hne]; exact r6 p hp
  · rw [ht.other _ (by decide), k6.1 _ (by decide), k5.1 _ (by decide), k4.regs.1 _ (by decide),
      k3.regs.1 _ (by decide), k2.regs.1 _ (by decide), k1.regs.1 _ (by decide)]
  · rw [ht.mem, m6, m5]
    exact (((k1.mem.whole (by decide) (by decide)).trans (k2.mem.widen.whole (by decide) (by decide))).trans
      (k3.mem.whole (by decide) (by decide))).trans (k4.mem.widen.whole (by decide) (by decide))

end VG.Proof.Ed448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.VerifyLocal`. -/
section

/-!
# Ed448 verification's equation on x86 (32-bit): the contract the proof is written against

`verifyEquationLocal`, the facts of `Spec.Ed448.verifyEquationContract` the
proof is written against, in a module of their own: callers proven for any
code meeting it need not import the proof. The arguments are only read; the
inputs are public (`pub` includes their bytes).
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86
open VG.Spec.Ed448 (bytesAt)

/-- `vg_ed448_verify_equation(pk, signature, challenge, scratch) -> eax`,
whose arguments are on the stack (cdecl). -/
def verifyEquationLocal : Contract isa where
  pre s :=
    let pk : Region := ⟨(arg s 0).setWidth 64, 57⟩
    let sig : Region := ⟨(arg s 1).setWidth 64, 114⟩
    let challenge : Region := ⟨(arg s 2).setWidth 64, 57⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [pk, sig, challenge, args] ∧ s.wr = [scratch] ∧
      pk.Disjoint scratch ∧ sig.Disjoint scratch ∧ challenge.Disjoint scratch ∧
      args.Disjoint scratch ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 57 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 114 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 57 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 8192 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  post s t := t.gpr .eax = if Spec.Ed448.verifyEquation
    (VG.Spec.Ed448.bytesAt s.mem ((arg s 0).setWidth 64) 57) (VG.Spec.Ed448.bytesAt s.mem ((arg s 1).setWidth 64) 114)
    (VG.Spec.Ed448.bytesAt s.mem ((arg s 2).setWidth 64) 57) then 1 else 0
  pub s t := s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧
    arg s 2 = arg t 2 ∧ arg s 3 = arg t 3 ∧
    VG.Spec.Ed448.bytesAt s.mem ((arg s 0).setWidth 64) 57 = VG.Spec.Ed448.bytesAt t.mem ((arg t 0).setWidth 64) 57 ∧
    VG.Spec.Ed448.bytesAt s.mem ((arg s 1).setWidth 64) 114 = VG.Spec.Ed448.bytesAt t.mem ((arg t 1).setWidth 64) 114 ∧
    VG.Spec.Ed448.bytesAt s.mem ((arg s 2).setWidth 64) 57 = VG.Spec.Ed448.bytesAt t.mem ((arg t 2).setWidth 64) 57

end VG.Proof.Ed448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.VerifyLoop`. -/
section

/-!
# Ed448 verification's equation on x86 (32-bit): `[S]B + [k](-A)`

One iteration of `vloop` (`vstep_ok`), for bit `t` of `S` and of `k` (bits 0
and 1 of byte `t` at `BITS`): `Q` (slots 0–2) doubled, then `B` (slots 8–10)
added and swapped in by the first bit, and `-A` (slots 6, 7 and 10) by the
second, with the shared formulas (`Proof/Ed448/VerifyFormulas.lean`). The
loop's invariant (`VInv`): `Q` is the reference ladder's point after the bits
above `n` (`Proof.Ed448.vladder`).
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Impl.Ed448 VG.Impl.Ed448.X86 VG.Proof.X448.X86
open VG.Proof.Ed448 (double vladder vstepRef vladder_bit bitAt evalOps pt addWith)
open VG.Impl.X448.X86 (BITS slot ACC at_)

/-! ## The values -/

/-- The slots after a swap of `T` into `Q`. -/
def swapEnv (sw : Bool) (e : Env) : Env := opSwap 2 5 sw (opSwap 1 4 sw (opSwap 0 3 sw e))

/-- The slots after an iteration, for the bits `sw₁` (of `S`) and `sw₂` (of `k`). -/
def vstepEnv (sw₁ sw₂ : Bool) (e : Env) : Env :=
  VG.Proof.Ed448.X86.swapEnv sw₂ (evalOps (VG.Impl.Ed448.addAt 6 7) (VG.Proof.Ed448.X86.swapEnv sw₁ (evalOps (VG.Impl.Ed448.addAt 8 9) (evalOps (doubleAt 0 1 2) e))))

theorem swapEnv_keep (sw : Bool) (e : Env) (i : Index) (hi : 6 ≤ i.val) :
    VG.Proof.Ed448.X86.swapEnv sw e i = e i := by
  have h0 : i ≠ 0 := fun h => by subst h; omega
  have h1 : i ≠ 1 := fun h => by subst h; omega
  have h2 : i ≠ 2 := fun h => by subst h; omega
  have h3 : i ≠ 3 := fun h => by subst h; omega
  have h4 : i ≠ 4 := fun h => by subst h; omega
  have h5 : i ≠ 5 := fun h => by subst h; omega
  simp only [VG.Proof.Ed448.X86.swapEnv, opSwap, Function.update_of_ne h0, Function.update_of_ne h2, Function.update_of_ne h3,
    Function.update_of_ne h4, Function.update_of_ne h5, Function.update_of_ne h1]

theorem pt_swap (sw : Bool) (e : Env) :
    pt (VG.Proof.Ed448.X86.swapEnv sw e) 0 1 2 = if sw then pt e 3 4 5 else pt e 0 1 2 := by
  cases sw <;> rfl

theorem vstepEnv_pt (sw₁ sw₂ : Bool) (e : Env) :
    pt (VG.Proof.Ed448.X86.vstepEnv sw₁ sw₂ e) 0 1 2 =
      let r₁ := double (pt e 0 1 2)
      let r₂ := if sw₁ then addWith (e 11) r₁ (pt e 8 9 10) else r₁
      if sw₂ then addWith (e 11) r₂ (pt e 6 7 10) else r₂ := by
  unfold VG.Proof.Ed448.X86.vstepEnv
  generalize he0 : evalOps (doubleAt 0 1 2) e = e0
  have p0 : pt e0 0 1 2 = double (pt e 0 1 2) := by rw [← he0, Proof.Ed448.doubleAt_eval0]
  have k0 : ∀ i : Index, 3 ≤ i.val ∧ i.val < 12 → e0 i = e i := fun i hi => by
    rw [← he0, Proof.Ed448.doubleAt_keep0 _ _ (Or.inl hi)]
  generalize he1 : evalOps (VG.Impl.Ed448.addAt 8 9) e0 = e1
  have p1 : pt e1 3 4 5 = addWith (e0 11) (pt e0 0 1 2) (pt e0 8 9 10) := by
    rw [← he1, Proof.Ed448.addAt_eval8]
  have q1 : pt e1 0 1 2 = pt e0 0 1 2 :=
    VG.Proof.Ed448.X86.pt_congr' (by rw [← he1, Proof.Ed448.addAt_keep _ _ _ _ (Or.inl (by decide))])
      (by rw [← he1, Proof.Ed448.addAt_keep _ _ _ _ (Or.inl (by decide))])
      (by rw [← he1, Proof.Ed448.addAt_keep _ _ _ _ (Or.inl (by decide))])
  have k1 : ∀ i : Index, 6 ≤ i.val ∧ i.val < 12 → e1 i = e0 i := fun i hi => by
    rw [← he1, Proof.Ed448.addAt_keep _ _ _ _ (Or.inr (Or.inl hi))]
  generalize he2 : VG.Proof.Ed448.X86.swapEnv sw₁ e1 = e2
  have p2 : pt e2 0 1 2 = if sw₁ then pt e1 3 4 5 else pt e1 0 1 2 := by rw [← he2, VG.Proof.Ed448.X86.pt_swap]
  have k2 : ∀ i : Index, 6 ≤ i.val ∧ i.val < 12 → e2 i = e1 i := fun i hi => by
    rw [← he2, VG.Proof.Ed448.X86.swapEnv_keep _ _ _ hi.1]
  generalize he3 : evalOps (VG.Impl.Ed448.addAt 6 7) e2 = e3
  have p3 : pt e3 3 4 5 = addWith (e2 11) (pt e2 0 1 2) (pt e2 6 7 10) := by
    rw [← he3, Proof.Ed448.addAt_eval6]
  have q3 : pt e3 0 1 2 = pt e2 0 1 2 :=
    VG.Proof.Ed448.X86.pt_congr' (by rw [← he3, Proof.Ed448.addAt_keep _ _ _ _ (Or.inl (by decide))])
      (by rw [← he3, Proof.Ed448.addAt_keep _ _ _ _ (Or.inl (by decide))])
      (by rw [← he3, Proof.Ed448.addAt_keep _ _ _ _ (Or.inl (by decide))])
  have e11 : e2 11 = e 11 := by rw [k2 11 (by decide), k1 11 (by decide), k0 11 (by decide)]
  have e11' : e0 11 = e 11 := k0 11 (by decide)
  have b8 : pt e0 8 9 10 = pt e 8 9 10 :=
    VG.Proof.Ed448.X86.pt_congr' (k0 8 (by decide)) (k0 9 (by decide)) (k0 10 (by decide))
  have a6 : pt e2 6 7 10 = pt e 6 7 10 :=
    VG.Proof.Ed448.X86.pt_congr' (by rw [k2 6 (by decide), k1 6 (by decide), k0 6 (by decide)])
      (by rw [k2 7 (by decide), k1 7 (by decide), k0 7 (by decide)])
      (by rw [k2 10 (by decide), k1 10 (by decide), k0 10 (by decide)])
  rw [VG.Proof.Ed448.X86.pt_swap, p3, q3, p2, p1, q1, e11, e11', b8, a6, p0]

theorem vstepEnv_keep (sw₁ sw₂ : Bool) (e : Env) (i : Index) (hi : 6 ≤ i.val ∧ i.val < 12) :
    VG.Proof.Ed448.X86.vstepEnv sw₁ sw₂ e i = e i := by
  rw [VG.Proof.Ed448.X86.vstepEnv, VG.Proof.Ed448.X86.swapEnv_keep _ _ _ hi.1, Proof.Ed448.addAt_keep _ _ _ _ (Or.inr (Or.inl hi)),
    VG.Proof.Ed448.X86.swapEnv_keep _ _ _ hi.1, Proof.Ed448.addAt_keep _ _ _ _ (Or.inr (Or.inl hi)),
    Proof.Ed448.doubleAt_keep0 _ _ (Or.inl ⟨by omega, hi.2⟩)]

/-- One bit of both scalars: the reference ladder's point after the bits above
`t`, then after bit `t`. -/
theorem vladder_step {e : Env} {S K t : Nat} {A : Spec.Ed448.Point} (ht : t < 456)
    (hr : pt e 0 1 2 = vladder S K A (456 - (t + 1)))
    (hq : pt e 8 9 10 = Spec.Ed448.basePoint) (ha : pt e 6 7 10 = A) (hd : e 11 = Spec.Ed448.d) :
    pt (VG.Proof.Ed448.X86.vstepEnv (decide ((S >>> t) &&& 1 = 1)) (decide ((K >>> t) &&& 1 = 1)) e) 0 1 2 =
      vladder S K A (456 - t) := by
  rw [VG.Proof.Ed448.X86.vstepEnv_pt, hd, hq, ha, hr, vladder_bit S K A ht]
  rfl

/-! ## One iteration -/

theorem pair_mask : ∀ a < 2, ∀ b < 2,
    (0 : BitVec 32) - ((BitVec.ofNat 8 (a + 2 * b)).setWidth 32 &&& 1) = VG.Proof.X448.X86.mask (decide (a = 1)) ∧
    (0 : BitVec 32) - ((BitVec.ofNat 8 (a + 2 * b)).setWidth 32 >>> 1) = VG.Proof.X448.X86.mask (decide (b = 1)) := by
  decide

theorem vmask_ok {s : State} {base : Addr} (hs : Scr s base) {t : Nat} (ht : t < 456)
    (hb : s.gpr .esi = BitVec.ofNat 32 t) {a b : Nat} (ha : a < 2) (hb2 : b < 2)
    (hbit : s.mem (off base (VG.Impl.X448.X86.BITS + t)) = BitVec.ofNat 8 (a + 2 * b)) (hi : Bool) :
    WP isa (.block (vmask hi)) s fun u =>
      u.gpr .ebx = VG.Proof.X448.X86.mask (decide ((if hi then b else a) = 1)) ∧ Keeps workRegs s u ∧ u.mem = s.mem := by
  have hB : VG.Impl.X448.X86.BITS = 3072 := rfl
  unfold vmask
  refine VG.Proof.X448.X86.wp_mov rfl fun u1 v1 => wp_alu (Or.inl rfl) rfl fun u2 v2 _ => ?_
  have ba : u2.ea (VG.Impl.X448.X86.at_ .ebp VG.Impl.X448.X86.BITS) = off base (VG.Impl.X448.X86.BITS + t) := by
    change (u2.gpr .ebp + BitVec.ofNat 32 VG.Impl.X448.X86.BITS).setWidth 64 = _
    rw [v2.gpr]; change (u1.gpr .ebp + u1.gpr .esi + BitVec.ofNat 32 VG.Impl.X448.X86.BITS).setWidth 64 = _
    rw [v1.gpr, v1.other .esi (by decide), hb, Offset.add_add, Nat.add_comm t VG.Impl.X448.X86.BITS]
    exact hs.ea (by omega)
  refine wp_load8 ba (by rw [v2.rd, v2.wr, v1.rd, v1.wr]; exact hs.read (by omega)) fun u3 v3 => ?_
  have e3 : u3.gpr .eax = (BitVec.ofNat 8 (a + 2 * b)).setWidth 32 := by rw [v3.gpr, v2.mem, v1.mem, hbit]
  have pm := VG.Proof.Ed448.X86.pair_mask a ha b hb2
  have k3 : Keeps workRegs s u3 :=
    (v1.rest (by decide)).trans ((v2.rest (by decide)).trans (v3.rest (by decide)))
  have m3 : u3.mem = s.mem := by rw [v3.mem, v2.mem, v1.mem]
  cases hi
  · refine wp_alu (Or.inr (Or.inr (Or.inl rfl))) rfl fun u4 v4 _ => ?_
    refine VG.Proof.X448.X86.wp_mov rfl fun u5 v5 => wp_alu (Or.inr (Or.inl rfl)) rfl fun u6 v6 _ =>
      WP.block_nil ⟨?_, ?_, ?_⟩
    · rw [v6.gpr]; change u5.gpr .ebx - u5.gpr .eax = _
      rw [v5.gpr, v5.other _ (by decide), v4.gpr]
      change (0 : BitVec 32) - (u3.gpr .eax &&& 1) = _
      rw [e3]; exact pm.1
    · exact k3.trans ((v4.rest (by decide)).trans ((v5.rest (by decide)).trans (v6.rest (by decide))))
    · rw [v6.mem, v5.mem, v4.mem, m3]
  · refine wp_shift (by decide) fun u4 v4 => ?_
    refine VG.Proof.X448.X86.wp_mov rfl fun u5 v5 => wp_alu (Or.inr (Or.inl rfl)) rfl fun u6 v6 _ =>
      WP.block_nil ⟨?_, ?_, ?_⟩
    · rw [v6.gpr]; change u5.gpr .ebx - u5.gpr .eax = _
      rw [v5.gpr, v5.other _ (by decide), v4.gpr]
      change (0 : BitVec 32) - (u3.gpr .eax >>> 1) = _
      rw [e3]; exact pm.2
    · exact k3.trans ((v4.rest (by decide)).trans ((v5.rest (by decide)).trans (v6.rest (by decide))))
    · rw [v6.mem, v5.mem, v4.mem, m3]

theorem swapT_ok {s : State} {base : Addr} (hs : Scr s base) (hbd : BoundedEnv s.mem base) {sw : Bool}
    (hc : s.gpr .ebx = VG.Proof.X448.X86.mask sw) :
    WP isa (.block swapT) s fun u => VG.Proof.X448.X86.Keep base s u ∧ BoundedEnv u.mem base ∧
      VG.Proof.X448.X86.E u.mem base = VG.Proof.Ed448.X86.swapEnv sw (VG.Proof.X448.X86.E s.mem base) := by
  unfold swapT
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (cswapE hs hbd 0 3 (by decide) hc) fun u1 ⟨k1, b1, c1, e1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cswapE (k1.scr hs) b1 1 4 (by decide) (c1.trans hc)) fun u2 ⟨k2, b2, c2, e2⟩ => ?_
  refine WP.mono (cswapE (k2.scr (k1.scr hs)) b2 2 5 (by decide) (c2.trans (c1.trans hc)))
    fun u3 ⟨k3, b3, _, e3⟩ => ⟨k1.trans (k2.trans k3), b3, by rw [e3, e2, e1]; rfl⟩

theorem vmaskSwap_ok {s : State} {base : Addr} (hs : Scr s base) (hbd : BoundedEnv s.mem base) {t : Nat}
    (ht : t < 456) (hb : s.gpr .esi = BitVec.ofNat 32 t) {a b : Nat} (ha : a < 2) (hb2 : b < 2)
    (hbit : s.mem (off base (VG.Impl.X448.X86.BITS + t)) = BitVec.ofNat 8 (a + 2 * b)) (hi : Bool) :
    WP isa (.block (vmask hi ++ swapT)) s fun u => VG.Proof.X448.X86.Keep base s u ∧ BoundedEnv u.mem base ∧
      VG.Proof.X448.X86.E u.mem base = VG.Proof.Ed448.X86.swapEnv (decide ((if hi then b else a) = 1)) (VG.Proof.X448.X86.E s.mem base) := by
  rw [WP.block_append_iff]
  exact WP.mono (VG.Proof.Ed448.X86.vmask_ok hs ht hb ha hb2 hbit hi) fun u ⟨c, k, m⟩ =>
    WP.mono (VG.Proof.Ed448.X86.swapT_ok (hs.of_keeps k (by decide)) (m ▸ hbd) c) fun v ⟨kv, bv, ev⟩ =>
      ⟨Keep.trans ⟨k, by rw [m]; exact Outside2.refl _ _ _ _ _ _⟩ kv, bv, by rw [ev, m]⟩

/-- The loop's invariant, after the bits above `n` of `S` and `k`, with `-A` the point `A`. -/
structure VInv (base : Addr) (S K : Nat) (A : Spec.Ed448.Point) (s₀ s : State) (n : Nat) : Prop where
  scr : Scr s base
  bounded : BoundedEnv s.mem base
  regs : Keeps (.esi :: workRegs) s₀ s
  esi : s.gpr .esi = BitVec.ofNat 32 n
  mem : Outside2 base 64 2816 ACC 512 s₀.mem s.mem
  rep : pt (VG.Proof.X448.X86.E s.mem base) 0 1 2 = vladder S K A (456 - n)
  q : pt (VG.Proof.X448.X86.E s.mem base) 8 9 10 = Spec.Ed448.basePoint
  na : pt (VG.Proof.X448.X86.E s.mem base) 6 7 10 = A
  d : VG.Proof.X448.X86.E s.mem base 11 = Spec.Ed448.d

theorem bit_lt' (k t : Nat) : (k >>> t) &&& 1 < 2 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem vstep_ok {s₀ s : State} {base : Addr} {S K : Nat} {A : Spec.Ed448.Point} {n : Nat} (hn : n < 456)
    (hbits : ∀ t < 456, s₀.mem (off base (VG.Impl.X448.X86.BITS + t)) = BitVec.ofNat 8 (VG.Proof.Ed448.X86.pair2 S K t))
    (hi : VG.Proof.Ed448.X86.VInv base S K A s₀ s (n + 1)) :
    WP isa vstep s fun t => VG.Proof.Ed448.X86.VInv base S K A s₀ t n ∧ t.zf = some (decide (n = 0)) := by
  have hs := hi.scr
  have hB : VG.Impl.X448.X86.BITS = 3072 := rfl
  have hA : ACC = 3584 := rfl
  have ha2 : (S >>> n) &&& 1 < 2 := VG.Proof.Ed448.X86.bit_lt' S n
  have hb2 : (K >>> n) &&& 1 < 2 := VG.Proof.Ed448.X86.bit_lt' K n
  have bitval : s.mem (off base (VG.Impl.X448.X86.BITS + n)) =
      BitVec.ofNat 8 (((S >>> n) &&& 1) + 2 * ((K >>> n) &&& 1)) := by
    rw [hi.mem _ (by rw [ofs_off' base (by omega)]; omega) (by rw [ofs_off' base (by omega)]; omega)]
    exact hbits n hn
  unfold vstep
  refine WP.seq (WP.mono (decCounter_ok (by omega) hi.esi) fun s₁ ⟨b₁, g₁, m₁, rd₁, wr₁, _⟩ => ?_)
  have K₁ : Keeps [.esi] s s₁ := ⟨fun r hr => g₁ r (fun h => hr (by simp [h])), rd₁, wr₁⟩
  have hs₁ := hs.of_keeps K₁ (by decide)
  refine VG.Proof.Ed448.X86.field_seq (doubleAt 0 1 2) Proof.Ed448.doubleAt_valid0 hs₁ (m₁ ▸ hi.bounded)
    fun s₂ k₂ bb₂ e₂ => ?_
  refine VG.Proof.Ed448.X86.field_seq (VG.Impl.Ed448.addAt 8 9) Proof.Ed448.addAt_valid8 (k₂.scr hs₁) bb₂ fun s₃ k₃ bb₃ e₃ => ?_
  have hs₃ := k₃.scr (k₂.scr hs₁)
  have b₃ : s₃.gpr .esi = BitVec.ofNat 32 n := by
    rw [k₃.regs.1 _ (by decide), k₂.regs.1 _ (by decide), b₁]
  have bit₃ : s₃.mem (off base (VG.Impl.X448.X86.BITS + n)) = BitVec.ofNat 8 (((S >>> n) &&& 1) + 2 * ((K >>> n) &&& 1)) := by
    rw [(k₂.trans k₃).mem _ (by rw [ofs_off' base (by omega)]; omega)
      (by rw [ofs_off' base (by omega)]; omega), m₁, bitval]
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86.vmaskSwap_ok hs₃ bb₃ hn b₃ ha2 hb2 bit₃ false) fun s₄ ⟨k₄, bb₄, e₄⟩ => ?_)
  have hs₄ := k₄.scr hs₃
  refine VG.Proof.Ed448.X86.field_seq (VG.Impl.Ed448.addAt 6 7) Proof.Ed448.addAt_valid6 hs₄ bb₄ fun s₅ k₅ bb₅ e₅ => ?_
  have hs₅ := k₅.scr hs₄
  have core4 := k₂.trans (k₃.trans (k₄.trans k₅))
  have b₅ : s₅.gpr .esi = BitVec.ofNat 32 n := by rw [core4.regs.1 _ (by decide), b₁]
  have bit₅ : s₅.mem (off base (VG.Impl.X448.X86.BITS + n)) = BitVec.ofNat 8 (((S >>> n) &&& 1) + 2 * ((K >>> n) &&& 1)) := by
    rw [core4.mem _ (by rw [ofs_off' base (by omega)]; omega)
      (by rw [ofs_off' base (by omega)]; omega), m₁, bitval]
  simp only [List.append_assoc]
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86.vmaskSwap_ok hs₅ bb₅ hn b₅ ha2 hb2 bit₅ true) fun s₆ ⟨k₆, bb₆, e₆⟩ => ?_
  refine VG.Proof.X448.X86.wp_cmp rfl fun t vt hz => WP.block_nil ?_
  have core := core4.trans k₆
  have b₆ : s₆.gpr .esi = BitVec.ofNat 32 n := by rw [core.regs.1 _ (by decide), b₁]
  have ee : VG.Proof.X448.X86.E t.mem base = VG.Proof.Ed448.X86.vstepEnv (decide ((S >>> n) &&& 1 = 1)) (decide ((K >>> n) &&& 1 = 1))
      (VG.Proof.X448.X86.E s.mem base) := by
    rw [vt.mem, e₆, e₅, e₄, e₃, e₂, m₁]; rfl
  have kk : ∀ i : Index, 6 ≤ i.val ∧ i.val < 12 → VG.Proof.X448.X86.E t.mem base i = VG.Proof.X448.X86.E s.mem base i := fun i h => by
    rw [ee, VG.Proof.Ed448.X86.vstepEnv_keep _ _ _ _ h]
  have K₆ : Keeps (.esi :: workRegs) s₆ t := vt.rest _
  refine ⟨⟨(core.scr hs₁).of_keeps K₆ (by decide), vt.mem ▸ bb₆, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · refine hi.regs.trans ⟨fun r hr => ?_, ?_, ?_⟩
    · rw [vt.gpr, core.regs.1 r (fun h => hr (List.mem_cons_of_mem _ h)), g₁ r (fun h => hr (by simp [h]))]
    · rw [vt.rd, core.regs.2.1, rd₁]
    · rw [vt.wr, core.regs.2.2, wr₁]
  · rw [vt.gpr, b₆]
  · refine hi.mem.trans ?_
    intro p hp hq
    rw [vt.mem, core.mem p hp hq, m₁]
  · rw [ee]; exact VG.Proof.Ed448.X86.vladder_step hn hi.rep hi.q hi.na hi.d
  · rw [VG.Proof.Ed448.X86.pt_congr' (kk 8 (by decide)) (kk 9 (by decide)) (kk 10 (by decide))]; exact hi.q
  · rw [VG.Proof.Ed448.X86.pt_congr' (kk 6 (by decide)) (kk 7 (by decide)) (kk 10 (by decide))]; exact hi.na
  · rw [kk 11 (by decide)]; exact hi.d
  · rw [hz, b₆, show BitVec.ofNat 32 n - (0 : BitVec 32) = BitVec.ofNat 32 n from BitVec.sub_zero _,
      VG.Proof.X448.X86.ofNat_beq_zero (by omega)]

theorem vloop_ok {s₀ s : State} {base : Addr} {S K : Nat} {A : Spec.Ed448.Point}
    (hbits : ∀ t < 456, s₀.mem (off base (VG.Impl.X448.X86.BITS + t)) = BitVec.ofNat 8 (VG.Proof.Ed448.X86.pair2 S K t))
    (hi : ∀ s', s'.gpr .esi = BitVec.ofNat 32 456 → (∀ r, r ≠ .esi → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → VG.Proof.Ed448.X86.VInv base S K A s₀ s' 456) :
    WP isa vloop s fun s' => VG.Proof.Ed448.X86.VInv base S K A s₀ s' 0 := by
  unfold vloop
  refine WP.seq (WP.mono (setCounter_ok s 456 (by decide)) fun s' ⟨h1, h2, h3, h4, h5⟩ => ?_)
  refine WP.loop (M := isa) (body := vstep) (c := .ne) (Q := fun s' => VG.Proof.Ed448.X86.VInv base S K A s₀ s' 0)
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 456 ∧ VG.Proof.Ed448.X86.VInv base S K A s₀ s m) ?_ 456 s'
    ⟨by decide, by decide, hi s' h1 h2 h3 h4 h5⟩
  intro m s ⟨h1, h2, hi⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine WP.mono (VG.Proof.Ed448.X86.vstep_ok (by omega) hbits hi) fun s' ⟨hi', hz⟩ => ?_
  simp only [eval, hz, Option.map_some]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, hi'⟩
  · refine .inr ⟨by simp only [decide_eq_false (by omega : ¬m = 0), Bool.not_false], m, by omega,
      by omega, by omega, hi'⟩

end VG.Proof.Ed448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.VerifyMain`. -/
section

/-!
# Ed448 verification's equation on x86 (32-bit): the whole function

`vg_ed448_verify_equation(pk = [esp + 4], signature = [esp + 8],
challenge = [esp + 12], scratch = [esp + 16])` returns `verifyEquation` of
its inputs (`verifyEquation_main`), given the reference computations'
agreement with the specification (`RecoverOk`, `VerifyEqOk`): the entry (the
registers saved, the bits of `S` and `k`, the check of `S`, the slots), `A`
decoded and negated, `Q = [S]B + [k](-A)` by the loop, `R` decoded, and the
comparison of `[4]Q` and `[4]R`. Every write is in the working space, so the
arguments and the inputs are read unchanged; the callee-saved registers are
restored from the working space, and the return address is kept.
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Impl.Ed448 VG.Impl.Ed448.X86 VG.Proof.X448.X86 VG.Proof.X448.Radix16
open VG.Proof.Ed448 (RecoverOk VerifyEqOk vladder negPoint double verifyEquation_none pt evalOps)
open VG.Impl.X448.X86 (slot X2 BITS ACC TMP at_ ops)
open VG.Spec.Ed448 (bytesAt decodeLE)

/-! ## The precondition and the arguments -/

/-- The precondition of `vg_ed448_verify_equation`, by name. -/
structure VerifyPre (s : State) : Prop where
  rd : s.rd = [⟨(arg s 0).setWidth 64, 57⟩, ⟨(arg s 1).setWidth 64, 114⟩, ⟨(arg s 2).setWidth 64, 57⟩,
    ⟨argAddr s 0, 16⟩]
  wr : s.wr = [scR (arg s 3)]
  pk_sc : (⟨(arg s 0).setWidth 64, 57⟩ : Region).Disjoint (scR (arg s 3))
  sig_sc : (⟨(arg s 1).setWidth 64, 114⟩ : Region).Disjoint (scR (arg s 3))
  ch_sc : (⟨(arg s 2).setWidth 64, 57⟩ : Region).Disjoint (scR (arg s 3))
  args_sc : (⟨argAddr s 0, 16⟩ : Region).Disjoint (scR (arg s 3))
  ret_sc : (VG.Proof.X448.X86.retR s).Disjoint (scR (arg s 3))
  f0 : (arg s 0).toNat + 57 ≤ 2 ^ 32
  f1 : (arg s 1).toNat + 114 ≤ 2 ^ 32
  f2 : (arg s 2).toNat + 57 ≤ 2 ^ 32
  f3 : (arg s 3).toNat + 8192 ≤ 2 ^ 32
  sp_fit : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32

theorem VerifyPre.of {s : State} (h : verifyEquationLocal.pre s) : VG.Proof.Ed448.X86.VerifyPre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem VerifyPre.args {s : State} (h : VG.Proof.Ed448.X86.VerifyPre s) : Args s 4 3 :=
  ⟨by rw [h.rd]; simp, by have := h.sp_fit; omega, by decide, by rw [h.wr]; simp, h.f3,
    h.args_sc, h.ret_sc⟩

/-- An argument's address, readable, and its value, in a later state. -/
theorem Args.argRead {s₀ s : State} {n sc : Nat} (hp : Args s₀ n sc) (hsp : s.gpr .esp = s₀.gpr .esp)
    (hr : s.rd = s₀.rd) (hw : s.wr = s₀.wr) (hm : Outside ((arg s₀ sc).setWidth 64) 0 8192 s₀.mem s.mem)
    {i : Nat} (hi : i < n) :
    s.ea (at_ .esp (4 + 4 * i)) = addr (s₀.gpr .esp) (4 + 4 * i) ∧
      InRegions (s.rd ++ s.wr) (addr (s₀.gpr .esp) (4 + 4 * i)) 4 ∧
      s.mem.readW (addr (s₀.gpr .esp) (4 + 4 * i)) 32 = arg s₀ i :=
  ⟨by change addr (s.gpr .esp) (4 + 4 * i) = _; rw [hsp],
    by rw [hr, hw]; exact ⟨_, List.mem_append_left _ hp.in_rd, hp.arg_contains hi⟩,
    hp.arg_same hm.frame hi⟩

/-! ## The bytes of the inputs -/

theorem bytesAt_take57 (m : Mem) (p : Addr) : (bytesAt m p 114).take 57 = bytesAt m p 57 := by
  simp [bytesAt, ← List.map_take, List.take_range]

theorem bytesAt_drop57 (m : Mem) (p : Addr) :
    (bytesAt m p 114).drop 57 = bytesAt m (p + BitVec.ofNat 64 57) 57 := by
  refine List.ext_getElem (by simp [bytesAt]) fun i _ _ => ?_
  simp only [bytesAt, List.getElem_drop, List.getElem_map, List.getElem_range]
  rw [Offset.add_add]

theorem bytesAt114_len (m : Mem) (p : Addr) : (bytesAt m p 114).length = 57 + 57 := by
  simp [bytesAt]

theorem bits_kept {base : Addr} {m m' : Mem} (h : Outside2 base 16 2864 ACC 512 m m') :
    ∀ t < 456, m' (off base (BITS + t)) = m (off base (BITS + t)) := fun t ht =>
  h _ (by rw [ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS]; omega)
    (by rw [ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS, ACC]; omega)

/-! ## The entry -/

theorem ventry_ok {s₀ : State} (h : VG.Proof.Ed448.X86.VerifyPre s₀) {base : Addr} (hbase : (arg s₀ 3).setWidth 64 = base) :
    WP isa (.block ventry) s₀ fun t =>
      Scr t base ∧ VG.Proof.X448.X86.Saved base s₀.gpr t.mem ∧ Outside base 0 8192 s₀.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s₀ t ∧
      VG.Proof.Ed448.X86.BadUpd (decodeLE (bytesAt s₀.mem ((arg s₀ 1).setWidth 64 + BitVec.ofNat 64 57) 57) < Spec.Ed448.L)
        0 (VG.Proof.X448.X86.word t.mem base BAD) ∧
      (∀ j < 456, t.mem (off base (BITS + j)) = BitVec.ofNat 8
        (VG.Proof.Ed448.X86.pair2 (decodeLE (bytesAt s₀.mem ((arg s₀ 1).setWidth 64 + BitVec.ofNat 64 57) 57))
          (decodeLE (bytesAt s₀.mem ((arg s₀ 2).setWidth 64) 57)) j)) ∧
      BoundedEnv t.mem base ∧ (∀ i : Index, E t.mem base i = Proof.X448.toFe (initVal i.val)) := by
  have hA := h.args
  have isig : Input s₀ base (arg s₀ 1) 114 := Input.of_region h.f1 (by rw [h.rd]; simp) (hbase ▸ h.sig_sc)
  have ich : Input s₀ base (arg s₀ 2) 57 := Input.of_region h.f2 (by rw [h.rd]; simp) (hbase ▸ h.ch_sc)
  unfold ventry
  simp only [List.append_assoc]
  -- The registers saved.
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86.save_ok hA) fun s₁ ⟨hs₁, sv₁, o₁, k₁⟩ => ?_
  rw [hbase] at hs₁ sv₁ o₁
  have o1w : Outside base 0 8192 s₀.mem s₁.mem := o₁.mono (by omega) (by omega)
  -- The bits.
  obtain ⟨e8, r8, v8⟩ := hA.argRead (k₁.1 _ (by decide)) k₁.2.1 k₁.2.2 (hbase ▸ o1w) (i := 1) (by decide)
  obtain ⟨e12, r12, v12⟩ := hA.argRead (k₁.1 _ (by decide)) k₁.2.1 k₁.2.2 (hbase ▸ o1w) (i := 2) (by decide)
  have rr1 : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [k₁.2.1, k₁.2.2]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86.vbits_ok hs₁ e8 r8 e12 r12 v8 v12 h.f1 h.f2
    (fun i hi => by rw [rr1, Offset.add_add]; exact isig.read _ (by omega))
    (fun i hi => by rw [rr1]; exact ich.read i hi)
    (fun i hi => by rw [Offset.add_add]; exact isig.far _ (by omega)) ich.far)
    fun s₂ ⟨esi₂, k₂, o₂, b₂⟩ => ?_
  have bs : bytesAt s₁.mem ((arg s₀ 1).setWidth 64 + BitVec.ofNat 64 57) 57 =
      bytesAt s₀.mem ((arg s₀ 1).setWidth 64 + BitVec.ofNat 64 57) 57 := by
    simp only [bytesAt]
    refine List.map_congr_left fun i hi => o1w _ (Or.inr ?_)
    simp only [List.mem_range] at hi
    rw [Offset.add_add]; exact isig.far _ (by omega)
  rw [bs, ich.bytes o1w] at b₂
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  -- `BAD = 0`.
  refine wp_mov rfl fun s₃ v₃ => store_ok (hs₂.of_upd v₃ (by decide)) (by decide) fun s₄ v₄ => ?_
  have hs₄ := (hs₂.of_upd v₃ (by decide)).of_keeps (v₄.rest []) (by decide)
  have bad₄ : VG.Proof.X448.X86.word s₄.mem base BAD = 0 := by
    rw [v₄.mem, v₃.gpr]; exact Mem.readW_writeW_self32 _ _ _
  have o₄ : Outside base BAD 4 s₂.mem s₄.mem := by
    rw [v₄.mem, v₃.mem]; exact writeW_outside _ _ _ (by decide)
  -- The check of `S`.
  have esi₄ : s₄.gpr .esi = arg s₀ 1 := by rw [v₄.gpr, v₃.other _ (by decide), esi₂]
  have rr4 : s₄.rd ++ s₄.wr = s₀.rd ++ s₀.wr := by rw [v₄.rd, v₄.wr, v₃.rd, v₃.wr, k₂.2.1, k₂.2.2, rr1]
  have o04 : Outside base 0 8192 s₀.mem s₄.mem :=
    (o1w.trans (o₂.mono (by omega) (by simp only [BITS]; omega))).trans (o₄.mono (by omega) (by decide))
  change WP isa (.block (sCheck ++ initSlots)) s₄ _
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86.sCheck_ok hs₄ (q := (arg s₀ 1).setWidth 64 + BitVec.ofNat 64 57) (by rw [esi₄])
    (by rw [esi₄]; exact h.f1) (fun j hj => by rw [rr4, Offset.add_add]; exact isig.read _ (by omega))
    (fun j hj => by rw [Offset.add_add]; exact isig.far _ (by omega))) fun s₅ ⟨c₅, o₅, k₅⟩ => ?_
  have bS : bytesAt s₄.mem ((arg s₀ 1).setWidth 64 + BitVec.ofNat 64 57) 57 =
      bytesAt s₀.mem ((arg s₀ 1).setWidth 64 + BitVec.ofNat 64 57) 57 := by
    simp only [bytesAt]
    refine List.map_congr_left fun i hi => o04 _ (Or.inr ?_)
    simp only [List.mem_range] at hi
    rw [Offset.add_add]; exact isig.far _ (by omega)
  rw [bS, bad₄] at c₅
  have hs₅ := hs₄.of_keeps k₅ (by decide)
  -- The slots.
  refine WP.mono (VG.Proof.Ed448.X86.initSlots_ok hs₅) fun t ⟨lt, ot, kt⟩ => ?_
  have e : ∀ i : Index, E t.mem base i = Proof.X448.toFe (initVal i.val) := initSlots_E lt
  refine ⟨hs₅.of_keeps kt (by decide), ?_, ?_, ?_, ?_, fun j hj => ?_, initSlots_bounded lt, e⟩
  · exact (((sv₁.outside o₂ (by decide)).outside o₄ (by decide)).outside2 o₅ (by decide)
      (by decide)).outside ot (by decide)
  · exact (o04.trans (o₅.whole (by decide) (by decide))).trans (ot.mono (by omega) (by omega))
  · exact (k₁.mono (by decide)).trans ((k₂.mono (by decide)).trans ((v₃.rest (by decide)).trans
      ((v₄.rest _).trans ((k₅.mono (by decide)).trans (kt.mono (by decide))))))
  · refine c₅.of_eq ?_
    exact ot.word (Or.inl (by decide)) (by decide)
  · rw [ot _ (Or.inr (by rw [ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS]; omega)),
      o₅ _ (by rw [ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS, TMP]; omega)
        (by rw [ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS, BAD]; omega),
      o₄ _ (by rw [ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS, BAD]; omega)]
    exact b₂ j hj

/-! ## The whole function -/

theorem sub6_E (e : Env) : evalOps [.sub 6 0 6] e 6 = e 0 - e 6 ∧ ∀ i : Index, i ≠ 6 → evalOps [.sub 6 0 6] e i = e i :=
  ⟨rfl, fun _ hi => Function.update_of_ne hi _ _⟩

theorem verifyEquation_main (hR : RecoverOk) (hE : VerifyEqOk) {s₀ : State} (h : VG.Proof.Ed448.X86.VerifyPre s₀) :
    WP isa verifyEquation s₀ fun t => abiPreserved s₀ t ∧
      t.gpr .eax = if Spec.Ed448.verifyEquation (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) 57)
        (bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 114) (bytesAt s₀.mem ((arg s₀ 2).setWidth 64) 57)
        then 1 else 0 := by
  have hA := h.args
  obtain ⟨base, hbase⟩ : ∃ b, (arg s₀ 3).setWidth 64 = b := ⟨_, rfl⟩
  have ipk : Input s₀ base (arg s₀ 0) 57 := Input.of_region h.f0 (by rw [h.rd]; simp) (hbase ▸ h.pk_sc)
  have isig : Input s₀ base (arg s₀ 1) 114 := Input.of_region h.f1 (by rw [h.rd]; simp) (hbase ▸ h.sig_sc)
  obtain ⟨S, hS⟩ : ∃ S, decodeLE (bytesAt s₀.mem ((arg s₀ 1).setWidth 64 + BitVec.ofNat 64 57) 57) = S :=
    ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, decodeLE (bytesAt s₀.mem ((arg s₀ 2).setWidth 64) 57) = K := ⟨_, rfl⟩
  unfold verifyEquation
  -- The entry.
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86.ventry_ok h hbase) fun s₁ ⟨hs₁, sv₁, o₁, k₁, c₁, bits₁, b₁, e₁⟩ => ?_)
  rw [hS] at c₁ bits₁
  rw [hK] at bits₁
  obtain ⟨er, eq, ed⟩ := initE _ e₁
  have h10 : E s₁.mem base 10 = 1 := congrArg Spec.Ed448.Point.Z eq
  -- `A`.
  obtain ⟨a0e, a0r, a0v⟩ := hA.argRead (k₁.1 .esp (by decide)) k₁.2.1 k₁.2.2 (hbase ▸ o₁) (i := 0) (by decide)
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86.decode_ok hR hs₁ b₁ a0e a0r a0v h.f0
    (fun j hj => by rw [k₁.2.1, k₁.2.2]; exact ipk.read j hj) ipk.far 6 7 (Or.inl ⟨rfl, rfl⟩) h10 ed)
    fun s₂ ⟨k₂, b₂, c₂, v₂, e₂⟩ => ?_)
  rw [ipk.bytes o₁] at c₂ v₂
  have hs₂ := k₂.scr hs₁
  -- `-A`.
  refine VG.Proof.Ed448.X86.field_seq [.sub 6 0 6] (by decide) hs₂ b₂ fun s₃ k₃ b₃ e₃ => ?_
  have hs₃ := k₃.scr hs₂
  obtain ⟨n₃, k₃e⟩ := VG.Proof.Ed448.X86.sub6_E (E s₂.mem base)
  rw [← e₃] at n₃ k₃e
  -- `Q`'s `Y` set to 1.
  rw [show VG.Impl.X448.X86.ops [Impl.X448.X86.Op.copy X2 (slot 10)] = VG.Impl.X448.X86.ops (([.copy 1 10] : List FieldOp).map FieldOp.impl)
    from rfl]
  refine WP.seq (WP.mono (VG.Proof.X448.X86.ops_ok hs₃ b₃ [.copy 1 10]) fun s₄ ⟨k₄, b₄, e₄⟩ => ?_)
  have hs₄ := k₄.scr hs₃
  have e₄1 : E s₄.mem base 1 = E s₃.mem base 10 := by
    rw [e₄]; simp only [applyOps, FieldOp.apply, opCopy, Function.update_self]
  have e₄k : ∀ i : Index, i ≠ 1 → E s₄.mem base i = E s₃.mem base i := fun i hi => by
    rw [e₄]; exact Function.update_of_ne hi _ _
  -- What is kept from the entry to the loop.
  have k41 : ∀ i : Index, i.val = 0 ∨ i.val = 2 ∨ (8 ≤ i.val ∧ i.val ≤ 11) →
      E s₄.mem base i = E s₁.mem base i := fun i hi => by
    rw [e₄k i (fun h => by subst h; omega), k₃e i (fun h => by subst h; omega),
      e₂ i (fun h => by subst h; omega) (fun h => by subst h; omega) (by omega)]
  have O₄ : Outside base 0 8192 s₀.mem s₄.mem :=
    ((o₁.trans (k₂.mem.whole (by decide) (by decide))).trans (k₃.mem.whole (by decide) (by decide))).trans
      (k₄.mem.whole (by decide) (by decide))
  have bits₄ : ∀ t < 456, s₄.mem (off base (BITS + t)) = BitVec.ofNat 8 (VG.Proof.Ed448.X86.pair2 S K t) := fun t ht => by
    rw [VG.Proof.Ed448.X86.bits_kept (Outside2.widen k₄.mem) t ht, VG.Proof.Ed448.X86.bits_kept (Outside2.widen k₃.mem) t ht,
      VG.Proof.Ed448.X86.bits_kept k₂.mem t ht]
    exact bits₁ t ht
  -- The loop.
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86.vloop_ok (s₀ := s₄) (A := pt (E s₄.mem base) 6 7 10) bits₄
    (fun s' h1 h2 h3 h4 h5 => ?_)) fun s₅ I₅ => ?_)
  · have k' : Keeps (.esi :: workRegs) s₄ s' :=
      ⟨fun r hr => h2 r (fun e => hr (by subst r; exact List.mem_cons_self)), h4, h5⟩
    refine ⟨hs₄.of_keeps k' (by decide), h3 ▸ b₄, k', h1, h3 ▸ Outside2.refl _ _ _ _ _ _, ?_, ?_, ?_, ?_⟩
    · rw [h3, Nat.sub_self]
      show (⟨E s₄.mem base 0, E s₄.mem base 1, E s₄.mem base 2⟩ : Spec.Ed448.Point) = Spec.Ed448.identity
      rw [k41 0 (Or.inl rfl), k41 2 (Or.inr (Or.inl rfl)), e₄1, k₃e 10 (by decide),
        e₂ 10 (by decide) (by decide) (by decide), h10]
      rw [show E s₁.mem base 0 = Spec.Ed448.identity.X from congrArg Spec.Ed448.Point.X er,
        show E s₁.mem base 2 = Spec.Ed448.identity.Z from congrArg Spec.Ed448.Point.Z er]
      rfl
    · rw [h3, VG.Proof.Ed448.X86.pt_congr' (k41 8 (by decide)) (k41 9 (by decide)) (k41 10 (by decide))]; exact eq
    · rw [h3]
    · rw [h3, k41 11 (by decide)]; exact ed
  -- `Q`'s `Y` moved to slot 6.
  have hs₅ := I₅.scr
  rw [show VG.Impl.X448.X86.ops [Impl.X448.X86.Op.copy (slot 6) X2] = VG.Impl.X448.X86.ops (([.copy 6 1] : List FieldOp).map FieldOp.impl)
    from rfl]
  refine WP.seq (WP.mono (VG.Proof.X448.X86.ops_ok hs₅ I₅.bounded [.copy 6 1]) fun s₆ ⟨k₆, b₆, e₆⟩ => ?_)
  have hs₆ := k₆.scr hs₅
  have e₆6 : E s₆.mem base 6 = E s₅.mem base 1 := by
    rw [e₆]; simp only [applyOps, FieldOp.apply, opCopy, Function.update_self]
  have e₆k : ∀ i : Index, i ≠ 6 → E s₆.mem base i = E s₅.mem base i := fun i hi => by
    rw [e₆]; exact Function.update_of_ne hi _ _
  have O₆ : Outside base 0 8192 s₀.mem s₆.mem :=
    (O₄.trans (I₅.mem.whole (by decide) (by decide))).trans (k₆.mem.whole (by decide) (by decide))
  have k06 : Keeps (.esi :: workRegs) s₁ s₆ :=
    ((k₂.regs.trans (k₃.regs.mono (fun _ h => List.mem_cons_of_mem _ h))).trans
      (k₄.regs.mono (fun _ h => List.mem_cons_of_mem _ h))).trans
      (I₅.regs.trans (k₆.regs.mono (fun _ h => List.mem_cons_of_mem _ h)))
  -- `R`.
  obtain ⟨a1e, a1r, a1v⟩ := hA.argRead (s := s₆) (by rw [k06.1 _ (by decide), k₁.1 _ (by decide)])
    (by rw [k06.2.1, k₁.2.1]) (by rw [k06.2.2, k₁.2.2]) (hbase ▸ O₆) (i := 1) (by decide)
  have h106 : E s₆.mem base 10 = 1 := by rw [e₆k 10 (by decide)]; exact congrArg Spec.Ed448.Point.Z I₅.q
  have d₆ : E s₆.mem base 11 = Spec.Ed448.d := by rw [e₆k 11 (by decide)]; exact I₅.d
  refine WP.seq (WP.mono (VG.Proof.Ed448.X86.decode_ok hR hs₆ b₆ a1e a1r a1v (by have := h.f1; omega)
    (fun j hj => by rw [k06.2.1, k06.2.2, k₁.2.1, k₁.2.2]; exact isig.read j (by omega))
    (fun j hj => isig.far j (by omega)) 8 9 (Or.inr ⟨rfl, rfl⟩) h106 d₆)
    fun s₇ ⟨k₇, b₇, c₇, v₇, e₇⟩ => ?_)
  have bR : bytesAt s₆.mem ((arg s₀ 1).setWidth 64) 57 = bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 57 := by
    simp only [bytesAt]
    refine List.map_congr_left fun i hi => O₆ _ (Or.inr ?_)
    simp only [List.mem_range] at hi
    exact isig.far i (by omega)
  rw [bR, ← VG.Proof.Ed448.X86.bytesAt_take57] at c₇ v₇
  have hs₇ := k₇.scr hs₆
  -- `BAD`.
  have bad₄ : VG.Proof.X448.X86.word s₄.mem base BAD = VG.Proof.X448.X86.word s₂.mem base BAD := by rw [Keep.bad k₄, Keep.bad k₃]
  have bad₆ : VG.Proof.X448.X86.word s₆.mem base BAD = VG.Proof.X448.X86.word s₄.mem base BAD := by
    rw [Keep.bad k₆]; exact I₅.mem.word (Or.inl (by decide)) (Or.inl (by decide)) (by decide)
  have c₇' : VG.Proof.Ed448.X86.BadUpd ((Spec.Ed448.decodePoint ((bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 114).take 57)).isSome)
      (VG.Proof.X448.X86.word s₂.mem base BAD) (VG.Proof.X448.X86.word s₇.mem base BAD) := by
    rw [← bad₄, ← bad₆]; exact c₇
  have z₇ := ((c₁.trans c₂).trans c₇').zero
  -- The comparison.
  have sv₇ : VG.Proof.X448.X86.Saved base s₀.gpr s₇.mem :=
    (((((sv₁.outside2 k₂.mem (by decide) (by decide)).outside2 k₃.mem (by decide) (by decide)).outside2
      k₄.mem (by decide) (by decide)).outside2 I₅.mem (by decide) (by decide)).outside2 k₆.mem (by decide)
      (by decide)).outside2 k₇.mem (by decide) (by decide)
  refine WP.mono (VG.Proof.Ed448.X86.vfinish_ok hs₇ b₇ sv₇ z₇.2) fun t ⟨rt, st, spt, ot⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact st (.ebx, 0) (by decide)
    · exact st (.esi, 4) (by decide)
    · exact st (.edi, 8) (by decide)
    · exact st (.ebp, 12) (by decide)
    · rw [spt, k₇.regs.1 _ (by decide), k06.1 _ (by decide), k₁.1 _ (by decide)]
  · have O₇ : Outside base 0 8192 s₀.mem t.mem :=
      (O₆.trans (k₇.mem.whole (by decide) (by decide))).trans ot
    have frame : Frame [⟨base, 8192⟩] s₀.mem t.mem := Outside.frame O₇
    have ret : (VG.Proof.X448.X86.retR s₀).Contains ((s₀.gpr .esp).setWidth 64) 4 := by
      simpa only [BitVec.add_zero] using
        Offset.contains_base ((s₀.gpr .esp).setWidth 64) (d := 0) (n := 4) (k := 4) (by decide)
          (by decide)
    exact frame.readW ret
      (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          subst hr; exact hbase ▸ h.ret_sc) (by decide)
  · rw [rt]
    refine if_congr ?_ rfl rfl
    rw [z₇.1]
    cases ha : Spec.Ed448.decodePoint (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) 57) with
    | none =>
      rw [verifyEquation_none (Or.inl ha)]
      exact ⟨fun h => absurd h.1.1.2 (by simp), fun h => absurd h (by decide)⟩
    | some a =>
      cases hr : Spec.Ed448.decodePoint ((bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 114).take 57) with
      | none =>
        rw [verifyEquation_none (Or.inr hr)]
        exact ⟨fun h => absurd h.1.2 (by simp), fun h => absurd h (by decide)⟩
      | some r =>
        obtain ⟨ax, ay, az⟩ := v₂ a ha
        obtain ⟨rx, ry, rz⟩ := v₇ r hr
        have e20 : E s₂.mem base 0 = 0 := by
          rw [e₂ 0 (by decide) (by decide) (Or.inl rfl)]; exact congrArg Spec.Ed448.Point.X er
        have e210 : E s₂.mem base 10 = 1 := by
          rw [e₂ 10 (by decide) (by decide) (by decide)]; exact h10
        have hA' : pt (E s₄.mem base) 6 7 10 = negPoint a := by
          show (⟨E s₄.mem base 6, E s₄.mem base 7, E s₄.mem base 10⟩ : Spec.Ed448.Point) = ⟨0 - a.X, a.Y, a.Z⟩
          rw [e₄k 6 (by decide), e₄k 7 (by decide), e₄k 10 (by decide), n₃, k₃e 7 (by decide),
            k₃e 10 (by decide), e20, ax, ay, e210, az]
        have hQ : pt (E s₇.mem base) 0 6 2 = vladder S K (negPoint a) 456 := by
          rw [VG.Proof.Ed448.X86.pt_congr' (e₇ 0 (by decide) (by decide) (Or.inl rfl)) (e₇ 6 (by decide) (by decide)
            (Or.inr (Or.inr ⟨by decide, by decide⟩))) (e₇ 2 (by decide) (by decide) (Or.inr (Or.inl rfl)))]
          show (⟨E s₆.mem base 0, E s₆.mem base 6, E s₆.mem base 2⟩ : Spec.Ed448.Point) = _
          rw [e₆k 0 (by decide), e₆6, e₆k 2 (by decide), ← hA']
          exact I₅.rep
        have hRR : pt (E s₇.mem base) 8 9 10 = r := by
          show (⟨E s₇.mem base 8, E s₇.mem base 9, E s₇.mem base 10⟩ : Spec.Ed448.Point) = r
          rw [rx, ry, e₇ 10 (by decide) (by decide) (by decide), h106, ← rz]
        rw [hE _ _ _ _ _ (VG.Proof.Ed448.X86.bytesAt57_len _ _) (VG.Proof.Ed448.X86.bytesAt114_len _ _) (VG.Proof.Ed448.X86.bytesAt57_len _ _) ha hr, hQ, hRR,
          VG.Proof.Ed448.X86.bytesAt_drop57, hS, hK]
        simp only [Option.isSome_some, and_true, Bool.and_eq_true, decide_eq_true_eq]

end VG.Proof.Ed448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.VerifyVerified`. -/
section

/-!
# Ed448 verification's equation on x86 (32-bit): `Verified`

Correctness including the ABI, given the reference computations' agreement
with the specification (`RecoverOk`, `VerifyEqOk`, which the registration
file passes in, from `Proof/Ed448/Facts.lean`), constant time (by taint
tracking: the only branches are on the loop counters, and every address is
an argument plus a constant or a counter), and a concrete state satisfying
the signature's contract. The contract lets timing depend on the inputs; the
code's depends on the pointers alone. The local contract only reads the
arguments; the shared one lets the code write them too (`writeArgs`), which
it does not (`Verified.narrowTo`).
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.X86
open VG.Proof.Ed448 (RecoverOk VerifyEqOk)
open VG.Impl.Ed448.X86 (verifyEquation)

/-- The taint analysis starts with the stack arguments public, and the word
holding `scratch` known to be the base address of the writable region. -/
def verifyTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [8192], argLen := 20, argBases := [(16, 0)] }

theorem verifyTaint_wf {s : State} (h : verifyEquationLocal.pre s) : VG.X86.Taint.Wf VG.Proof.Ed448.X86.verifyTaint s := by
  have hp := VerifyPre.of h
  have hf := hp.f3; have spfit := hp.sp_fit
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, VG.Proof.Ed448.X86.verifyTaint], by simp [hp.wr], ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [VG.Proof.Ed448.X86.verifyTaint]; omega, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl; simp only [BitVec.toNat_setWidth]; omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl
    exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.ret_sc hp.args_sc
  · intro p hp'
    simp only [VG.Proof.Ed448.X86.verifyTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    subst hp'
    exact ⟨by simp [VG.Proof.Ed448.X86.verifyTaint], by simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]⟩

theorem verifyTaint_agree {s t : State} (hs : verifyEquationLocal.pre s) (ht : verifyEquationLocal.pre t)
    (hp : verifyEquationLocal.pub s t) : VG.X86.Taint.Agree VG.Proof.Ed448.X86.verifyTaint s t := by
  obtain ⟨hsp, a0, a1, a2, a3, _⟩ := hp
  have ps := VerifyPre.of hs
  have pt := VerifyPre.of ht
  have ha : ∀ i < 4, arg s i = arg t i := fun i hi => by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
    exacts [a0, a1, a2, a3]
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, VG.Proof.Ed448.X86.verifyTaint_wf hs, VG.Proof.Ed448.X86.verifyTaint_wf ht,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hsp,
    fun k h4 hk => ?_⟩
  · simp only [VG.Proof.Ed448.X86.verifyTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hsp
  · rw [ps.wr, pt.wr, a3]
  · simp only [VG.Proof.Ed448.X86.verifyTaint] at hk
    have fs := ps.sp_fit
    have ft := pt.sp_fit
    rw [show VG.X86.Taint.depth verifyTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (by omega) h4 hk, VG.X86.Taint.argByte_eq (by omega) h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (ha ((k - 4) / 4) (by omega))

/-- Constant time: the entry block from `verifyTaint`, and the rest from
`fieldτ`, in one check with base-point multiplication's (`RestCT.lean`). -/
theorem verifyEquation_ct :
    ConstantTime isa verifyEquationLocal.pre verifyEquationLocal.pub verifyEquation :=
  RelCT.constantTime (relCT_split rfl VG.Proof.Ed448.X86.verifyTaint (fun _ _ h => VG.Proof.Ed448.X86.verifyTaint_agree h.1 h.2.1 h.2.2)
    (by taint_decide) verifyRest_ct)

theorem verifyEquation_ok (hR : RecoverOk) (hE : VerifyEqOk) (s : State) (h : verifyEquationLocal.pre s) :
    ∃ tr t, Exec isa verifyEquation s tr t ∧ abiPreserved s t ∧ verifyEquationLocal.post s t := by
  obtain ⟨tr, t, he, h1, h2⟩ := VG.Proof.Ed448.X86.verifyEquation_main hR hE (VerifyPre.of h)
  exact ⟨tr, t, he, h1, h2⟩

/-- Memory holding the arguments `0x1000, 0x2000, 0x3000, 0x4000` at `0x8004`. -/
def verifyEquationSatMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800d then 0x30
  else if a = 0x8011 then 0x40 else 0

/-- A state satisfying the shared contract's precondition. -/
def verifyEquationSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := VG.Proof.Ed448.X86.verifyEquationSatMem
  rd := [⟨0x1000, 57⟩, ⟨0x2000, 114⟩, ⟨0x3000, 57⟩]
  wr := [⟨0x4000, 8192⟩, ⟨0x8004, 16⟩]

/-- `verifyEquationLocal`, the arguments writable as the shared contract has them. -/
def verifyEquationWide : Contract isa :=
  { VG.Proof.Ed448.X86.verifyEquationLocal with
  pre := fun s =>
    let pk : Region := ⟨(arg s 0).setWidth 64, 57⟩
    let sig : Region := ⟨(arg s 1).setWidth 64, 114⟩
    let challenge : Region := ⟨(arg s 2).setWidth 64, 57⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [pk, sig, challenge] ∧ s.wr = [scratch, args] ∧
      pk.Disjoint scratch ∧ sig.Disjoint scratch ∧ challenge.Disjoint scratch ∧
      args.Disjoint scratch ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 57 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 114 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 57 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 8192 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 }

def verifyEquationRd (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, 57⟩, ⟨(arg s 1).setWidth 64, 114⟩, ⟨(arg s 2).setWidth 64, 57⟩,
    ⟨argAddr s 0, 16⟩]
def verifyEquationWr (s : State) : List Region := [⟨(arg s 3).setWidth 64, 8192⟩]

theorem verifyEquationWide_pre (s : State) (h : verifyEquationWide.pre s) :
    verifyEquationLocal.pre (s.withRegions (VG.Proof.Ed448.X86.verifyEquationRd s) (VG.Proof.Ed448.X86.verifyEquationWr s)) := by
  simp only [VG.Proof.Ed448.X86.verifyEquationLocal, VG.Proof.Ed448.X86.verifyEquationRd, VG.Proof.Ed448.X86.verifyEquationWr, arg_withRegions, argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr]
  exact ⟨True.intro, True.intro, h.2.2⟩

theorem byteMap_inj : ∀ {xs ys : List Byte}, xs.map (·.toNat) = ys.map (·.toNat) → xs = ys
  | [], [], _ => rfl
  | a :: xs, b :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, VG.Proof.Ed448.X86.byteMap_inj h.2]

theorem verifyEquationWide_implies :
    verifyEquationWide.Implies (Spec.Ed448.verifyEquationContract X86.abi) where
  pre := by
    sig_implies_pre [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, VG.Proof.Ed448.X86.verifyEquationWide, VG.Proof.Ed448.X86.verifyEquationLocal, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
  post s t _ h := by
    sig_post [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    change t.gpr .eax = _ at h
    rw [BitVec.setWidth_append_eq_right]
    exact h
  pub s t _ _ h := by
    sig_pub [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
    obtain ⟨sp, bytes, pk, sig, challenge, base⟩ := h
    have hb := VG.Proof.Ed448.X86.byteMap_inj bytes
    obtain ⟨first, last⟩ := List.append_inj' hb (by simp only [Spec.Ed448.bytesAt, List.length_map,
      List.length_range])
    obtain ⟨first, middle⟩ := List.append_inj' first (by simp only [Spec.Ed448.bytesAt, List.length_map,
      List.length_range])
    exact ⟨sp, pk, sig, challenge, base, first, middle, last⟩
  sat := by
    have a0 : arg VG.Proof.Ed448.X86.verifyEquationSat 0 = 0x1000 := by decide
    have a1 : arg VG.Proof.Ed448.X86.verifyEquationSat 1 = 0x2000 := by decide
    have a2 : arg VG.Proof.Ed448.X86.verifyEquationSat 2 = 0x3000 := by decide
    have a3 : arg VG.Proof.Ed448.X86.verifyEquationSat 3 = 0x4000 := by decide
    have e : argAddr VG.Proof.Ed448.X86.verifyEquationSat 0 = 0x8004 := by decide
    have esp : verifyEquationSat.gpr .esp = 0x8000 := rfl
    sig_implies_sat [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, VG.Proof.Ed448.X86.verifyEquationWide, VG.Proof.Ed448.X86.verifyEquationLocal, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] [a0, a1, a2, a3, e, esp] using VG.Proof.Ed448.X86.verifyEquationSat

theorem verifyEquation_verified (hR : RecoverOk) (hE : VerifyEqOk) :
    Verified X86.target verifyEquation (Spec.Ed448.verifyEquationContract X86.abi) := by
  have hsat := verifyEquationWide_implies.sat_left
  have satLocal : ∃ s, verifyEquationLocal.pre s := hsat.elim fun s h => ⟨_, VG.Proof.Ed448.X86.verifyEquationWide_pre s h⟩
  have verifiedLocal : Verified X86.target verifyEquation VG.Proof.Ed448.X86.verifyEquationLocal :=
    Verified.of_correct (VG.Proof.Ed448.X86.verifyEquation_ok hR hE) VG.Proof.Ed448.X86.verifyEquation_ct (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal VG.Proof.Ed448.X86.verifyEquationRd VG.Proof.Ed448.X86.verifyEquationWr
    VG.Proof.Ed448.X86.verifyEquationWide_pre ?_ ?_ ?_ ?_ hsat) VG.Proof.Ed448.X86.verifyEquationWide_implies
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [VG.Proof.Ed448.X86.verifyEquationRd, VG.Proof.Ed448.X86.verifyEquationWr, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with (rfl | rfl | rfl | rfl) | rfl <;> simp
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [VG.Proof.Ed448.X86.verifyEquationWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; simp
  · intro s t _ h
    exact h
  · intro s t _ _ h
    simpa only [VG.Proof.Ed448.X86.verifyEquationWide, VG.Proof.Ed448.X86.verifyEquationLocal, arg_withRegions, State.withRegions_gpr,
      State.withRegions_mem] using h

end VG.Proof.Ed448.X86

end

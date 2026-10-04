import VerifiedGarbage.Proof.Ed448.X86.VerifyField
import VerifiedGarbage.Proof.Ed448.X86.VerifyBits
import VerifiedGarbage.Proof.X448.X86.Counters

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
  swapEnv sw₂ (evalOps (addAt 6 7) (swapEnv sw₁ (evalOps (addAt 8 9) (evalOps (doubleAt 0 1 2) e))))

theorem swapEnv_keep (sw : Bool) (e : Env) (i : Index) (hi : 6 ≤ i.val) :
    swapEnv sw e i = e i := by
  have h0 : i ≠ 0 := fun h => by subst h; omega
  have h1 : i ≠ 1 := fun h => by subst h; omega
  have h2 : i ≠ 2 := fun h => by subst h; omega
  have h3 : i ≠ 3 := fun h => by subst h; omega
  have h4 : i ≠ 4 := fun h => by subst h; omega
  have h5 : i ≠ 5 := fun h => by subst h; omega
  simp only [swapEnv, opSwap, Function.update_of_ne h0, Function.update_of_ne h2, Function.update_of_ne h3,
    Function.update_of_ne h4, Function.update_of_ne h5, Function.update_of_ne h1]

theorem pt_swap (sw : Bool) (e : Env) :
    pt (swapEnv sw e) 0 1 2 = if sw then pt e 3 4 5 else pt e 0 1 2 := by
  cases sw <;> rfl

theorem vstepEnv_pt (sw₁ sw₂ : Bool) (e : Env) :
    pt (vstepEnv sw₁ sw₂ e) 0 1 2 =
      let r₁ := double (pt e 0 1 2)
      let r₂ := if sw₁ then addWith (e 11) r₁ (pt e 8 9 10) else r₁
      if sw₂ then addWith (e 11) r₂ (pt e 6 7 10) else r₂ := by
  unfold vstepEnv
  generalize he0 : evalOps (doubleAt 0 1 2) e = e0
  have p0 : pt e0 0 1 2 = double (pt e 0 1 2) := by rw [← he0, Proof.Ed448.doubleAt_eval0]
  have k0 : ∀ i : Index, 3 ≤ i.val ∧ i.val < 12 → e0 i = e i := fun i hi => by
    rw [← he0, Proof.Ed448.doubleAt_keep0 _ _ (Or.inl hi)]
  generalize he1 : evalOps (addAt 8 9) e0 = e1
  have p1 : pt e1 3 4 5 = addWith (e0 11) (pt e0 0 1 2) (pt e0 8 9 10) := by
    rw [← he1, Proof.Ed448.addAt_eval8]
  have q1 : pt e1 0 1 2 = pt e0 0 1 2 :=
    pt_congr' (by rw [← he1, Proof.Ed448.addAt_keep _ _ _ _ (Or.inl (by decide))])
      (by rw [← he1, Proof.Ed448.addAt_keep _ _ _ _ (Or.inl (by decide))])
      (by rw [← he1, Proof.Ed448.addAt_keep _ _ _ _ (Or.inl (by decide))])
  have k1 : ∀ i : Index, 6 ≤ i.val ∧ i.val < 12 → e1 i = e0 i := fun i hi => by
    rw [← he1, Proof.Ed448.addAt_keep _ _ _ _ (Or.inr (Or.inl hi))]
  generalize he2 : swapEnv sw₁ e1 = e2
  have p2 : pt e2 0 1 2 = if sw₁ then pt e1 3 4 5 else pt e1 0 1 2 := by rw [← he2, pt_swap]
  have k2 : ∀ i : Index, 6 ≤ i.val ∧ i.val < 12 → e2 i = e1 i := fun i hi => by
    rw [← he2, swapEnv_keep _ _ _ hi.1]
  generalize he3 : evalOps (addAt 6 7) e2 = e3
  have p3 : pt e3 3 4 5 = addWith (e2 11) (pt e2 0 1 2) (pt e2 6 7 10) := by
    rw [← he3, Proof.Ed448.addAt_eval6]
  have q3 : pt e3 0 1 2 = pt e2 0 1 2 :=
    pt_congr' (by rw [← he3, Proof.Ed448.addAt_keep _ _ _ _ (Or.inl (by decide))])
      (by rw [← he3, Proof.Ed448.addAt_keep _ _ _ _ (Or.inl (by decide))])
      (by rw [← he3, Proof.Ed448.addAt_keep _ _ _ _ (Or.inl (by decide))])
  have e11 : e2 11 = e 11 := by rw [k2 11 (by decide), k1 11 (by decide), k0 11 (by decide)]
  have e11' : e0 11 = e 11 := k0 11 (by decide)
  have b8 : pt e0 8 9 10 = pt e 8 9 10 :=
    pt_congr' (k0 8 (by decide)) (k0 9 (by decide)) (k0 10 (by decide))
  have a6 : pt e2 6 7 10 = pt e 6 7 10 :=
    pt_congr' (by rw [k2 6 (by decide), k1 6 (by decide), k0 6 (by decide)])
      (by rw [k2 7 (by decide), k1 7 (by decide), k0 7 (by decide)])
      (by rw [k2 10 (by decide), k1 10 (by decide), k0 10 (by decide)])
  rw [pt_swap, p3, q3, p2, p1, q1, e11, e11', b8, a6, p0]

theorem vstepEnv_keep (sw₁ sw₂ : Bool) (e : Env) (i : Index) (hi : 6 ≤ i.val ∧ i.val < 12) :
    vstepEnv sw₁ sw₂ e i = e i := by
  rw [vstepEnv, swapEnv_keep _ _ _ hi.1, Proof.Ed448.addAt_keep _ _ _ _ (Or.inr (Or.inl hi)),
    swapEnv_keep _ _ _ hi.1, Proof.Ed448.addAt_keep _ _ _ _ (Or.inr (Or.inl hi)),
    Proof.Ed448.doubleAt_keep0 _ _ (Or.inl ⟨by omega, hi.2⟩)]

/-- One bit of both scalars: the reference ladder's point after the bits above
`t`, then after bit `t`. -/
theorem vladder_step {e : Env} {S K t : Nat} {A : Spec.Ed448.Point} (ht : t < 456)
    (hr : pt e 0 1 2 = vladder S K A (456 - (t + 1)))
    (hq : pt e 8 9 10 = Spec.Ed448.basePoint) (ha : pt e 6 7 10 = A) (hd : e 11 = Spec.Ed448.d) :
    pt (vstepEnv (decide ((S >>> t) &&& 1 = 1)) (decide ((K >>> t) &&& 1 = 1)) e) 0 1 2 =
      vladder S K A (456 - t) := by
  rw [vstepEnv_pt, hd, hq, ha, hr, vladder_bit S K A ht]
  rfl

/-! ## One iteration -/

theorem pair_mask : ∀ a < 2, ∀ b < 2,
    (0 : BitVec 32) - ((BitVec.ofNat 8 (a + 2 * b)).setWidth 32 &&& 1) = mask (decide (a = 1)) ∧
    (0 : BitVec 32) - ((BitVec.ofNat 8 (a + 2 * b)).setWidth 32 >>> 1) = mask (decide (b = 1)) := by
  decide

theorem vmask_ok {s : State} {base : Addr} (hs : Scr s base) {t : Nat} (ht : t < 456)
    (hb : s.gpr .esi = BitVec.ofNat 32 t) {a b : Nat} (ha : a < 2) (hb2 : b < 2)
    (hbit : s.mem (off base (BITS + t)) = BitVec.ofNat 8 (a + 2 * b)) (hi : Bool) :
    WP isa (.block (vmask hi)) s fun u =>
      u.gpr .ebx = mask (decide ((if hi then b else a) = 1)) ∧ Keeps workRegs s u ∧ u.mem = s.mem := by
  have hB : BITS = 3072 := rfl
  unfold vmask
  refine wp_mov rfl fun u1 v1 => wp_alu (Or.inl rfl) rfl fun u2 v2 _ => ?_
  have ba : u2.ea (at_ .ebp BITS) = off base (BITS + t) := by
    change (u2.gpr .ebp + BitVec.ofNat 32 BITS).setWidth 64 = _
    rw [v2.gpr]; change (u1.gpr .ebp + u1.gpr .esi + BitVec.ofNat 32 BITS).setWidth 64 = _
    rw [v1.gpr, v1.other .esi (by decide), hb, Offset.add_add, Nat.add_comm t BITS]
    exact hs.ea (by omega)
  refine wp_load8 ba (by rw [v2.rd, v2.wr, v1.rd, v1.wr]; exact hs.read (by omega)) fun u3 v3 => ?_
  have e3 : u3.gpr .eax = (BitVec.ofNat 8 (a + 2 * b)).setWidth 32 := by rw [v3.gpr, v2.mem, v1.mem, hbit]
  have pm := pair_mask a ha b hb2
  have k3 : Keeps workRegs s u3 :=
    (v1.rest (by decide)).trans ((v2.rest (by decide)).trans (v3.rest (by decide)))
  have m3 : u3.mem = s.mem := by rw [v3.mem, v2.mem, v1.mem]
  cases hi
  · refine wp_alu (Or.inr (Or.inr (Or.inl rfl))) rfl fun u4 v4 _ => ?_
    refine wp_mov rfl fun u5 v5 => wp_alu (Or.inr (Or.inl rfl)) rfl fun u6 v6 _ =>
      WP.block_nil ⟨?_, ?_, ?_⟩
    · rw [v6.gpr]; change u5.gpr .ebx - u5.gpr .eax = _
      rw [v5.gpr, v5.other _ (by decide), v4.gpr]
      change (0 : BitVec 32) - (u3.gpr .eax &&& 1) = _
      rw [e3]; exact pm.1
    · exact k3.trans ((v4.rest (by decide)).trans ((v5.rest (by decide)).trans (v6.rest (by decide))))
    · rw [v6.mem, v5.mem, v4.mem, m3]
  · refine wp_shift (by decide) fun u4 v4 => ?_
    refine wp_mov rfl fun u5 v5 => wp_alu (Or.inr (Or.inl rfl)) rfl fun u6 v6 _ =>
      WP.block_nil ⟨?_, ?_, ?_⟩
    · rw [v6.gpr]; change u5.gpr .ebx - u5.gpr .eax = _
      rw [v5.gpr, v5.other _ (by decide), v4.gpr]
      change (0 : BitVec 32) - (u3.gpr .eax >>> 1) = _
      rw [e3]; exact pm.2
    · exact k3.trans ((v4.rest (by decide)).trans ((v5.rest (by decide)).trans (v6.rest (by decide))))
    · rw [v6.mem, v5.mem, v4.mem, m3]

theorem swapT_ok {s : State} {base : Addr} (hs : Scr s base) (hbd : BoundedEnv s.mem base) {sw : Bool}
    (hc : s.gpr .ebx = mask sw) :
    WP isa (.block swapT) s fun u => Keep base s u ∧ BoundedEnv u.mem base ∧
      E u.mem base = swapEnv sw (E s.mem base) := by
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
    (hbit : s.mem (off base (BITS + t)) = BitVec.ofNat 8 (a + 2 * b)) (hi : Bool) :
    WP isa (.block (vmask hi ++ swapT)) s fun u => Keep base s u ∧ BoundedEnv u.mem base ∧
      E u.mem base = swapEnv (decide ((if hi then b else a) = 1)) (E s.mem base) := by
  rw [WP.block_append_iff]
  exact WP.mono (vmask_ok hs ht hb ha hb2 hbit hi) fun u ⟨c, k, m⟩ =>
    WP.mono (swapT_ok (hs.of_keeps k (by decide)) (m ▸ hbd) c) fun v ⟨kv, bv, ev⟩ =>
      ⟨Keep.trans ⟨k, by rw [m]; exact Outside2.refl _ _ _ _ _ _⟩ kv, bv, by rw [ev, m]⟩

/-- The loop's invariant, after the bits above `n` of `S` and `k`, with `-A` the point `A`. -/
structure VInv (base : Addr) (S K : Nat) (A : Spec.Ed448.Point) (s₀ s : State) (n : Nat) : Prop where
  scr : Scr s base
  bounded : BoundedEnv s.mem base
  regs : Keeps (.esi :: workRegs) s₀ s
  esi : s.gpr .esi = BitVec.ofNat 32 n
  mem : Outside2 base 64 2816 ACC 512 s₀.mem s.mem
  rep : pt (E s.mem base) 0 1 2 = vladder S K A (456 - n)
  q : pt (E s.mem base) 8 9 10 = Spec.Ed448.basePoint
  na : pt (E s.mem base) 6 7 10 = A
  d : E s.mem base 11 = Spec.Ed448.d

theorem bit_lt' (k t : Nat) : (k >>> t) &&& 1 < 2 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem vstep_ok {s₀ s : State} {base : Addr} {S K : Nat} {A : Spec.Ed448.Point} {n : Nat} (hn : n < 456)
    (hbits : ∀ t < 456, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (pair2 S K t))
    (hi : VInv base S K A s₀ s (n + 1)) :
    WP isa vstep s fun t => VInv base S K A s₀ t n ∧ t.zf = some (decide (n = 0)) := by
  have hs := hi.scr
  have hB : BITS = 3072 := rfl
  have hA : ACC = 3584 := rfl
  have ha2 : (S >>> n) &&& 1 < 2 := bit_lt' S n
  have hb2 : (K >>> n) &&& 1 < 2 := bit_lt' K n
  have bitval : s.mem (off base (BITS + n)) =
      BitVec.ofNat 8 (((S >>> n) &&& 1) + 2 * ((K >>> n) &&& 1)) := by
    rw [hi.mem _ (by rw [ofs_off' base (by omega)]; omega) (by rw [ofs_off' base (by omega)]; omega)]
    exact hbits n hn
  unfold vstep
  refine WP.seq (WP.mono (decCounter_ok (by omega) hi.esi) fun s₁ ⟨b₁, g₁, m₁, rd₁, wr₁, _⟩ => ?_)
  have K₁ : Keeps [.esi] s s₁ := ⟨fun r hr => g₁ r (fun h => hr (by simp [h])), rd₁, wr₁⟩
  have hs₁ := hs.of_keeps K₁ (by decide)
  refine field_seq (doubleAt 0 1 2) Proof.Ed448.doubleAt_valid0 hs₁ (m₁ ▸ hi.bounded)
    fun s₂ k₂ bb₂ e₂ => ?_
  refine field_seq (addAt 8 9) Proof.Ed448.addAt_valid8 (k₂.scr hs₁) bb₂ fun s₃ k₃ bb₃ e₃ => ?_
  have hs₃ := k₃.scr (k₂.scr hs₁)
  have b₃ : s₃.gpr .esi = BitVec.ofNat 32 n := by
    rw [k₃.regs.1 _ (by decide), k₂.regs.1 _ (by decide), b₁]
  have bit₃ : s₃.mem (off base (BITS + n)) = BitVec.ofNat 8 (((S >>> n) &&& 1) + 2 * ((K >>> n) &&& 1)) := by
    rw [(k₂.trans k₃).mem _ (by rw [ofs_off' base (by omega)]; omega)
      (by rw [ofs_off' base (by omega)]; omega), m₁, bitval]
  refine WP.seq (WP.mono (vmaskSwap_ok hs₃ bb₃ hn b₃ ha2 hb2 bit₃ false) fun s₄ ⟨k₄, bb₄, e₄⟩ => ?_)
  have hs₄ := k₄.scr hs₃
  refine field_seq (addAt 6 7) Proof.Ed448.addAt_valid6 hs₄ bb₄ fun s₅ k₅ bb₅ e₅ => ?_
  have hs₅ := k₅.scr hs₄
  have core4 := k₂.trans (k₃.trans (k₄.trans k₅))
  have b₅ : s₅.gpr .esi = BitVec.ofNat 32 n := by rw [core4.regs.1 _ (by decide), b₁]
  have bit₅ : s₅.mem (off base (BITS + n)) = BitVec.ofNat 8 (((S >>> n) &&& 1) + 2 * ((K >>> n) &&& 1)) := by
    rw [core4.mem _ (by rw [ofs_off' base (by omega)]; omega)
      (by rw [ofs_off' base (by omega)]; omega), m₁, bitval]
  simp only [List.append_assoc]
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (vmaskSwap_ok hs₅ bb₅ hn b₅ ha2 hb2 bit₅ true) fun s₆ ⟨k₆, bb₆, e₆⟩ => ?_
  refine wp_cmp rfl fun t vt hz => WP.block_nil ?_
  have core := core4.trans k₆
  have b₆ : s₆.gpr .esi = BitVec.ofNat 32 n := by rw [core.regs.1 _ (by decide), b₁]
  have ee : E t.mem base = vstepEnv (decide ((S >>> n) &&& 1 = 1)) (decide ((K >>> n) &&& 1 = 1))
      (E s.mem base) := by
    rw [vt.mem, e₆, e₅, e₄, e₃, e₂, m₁]; rfl
  have kk : ∀ i : Index, 6 ≤ i.val ∧ i.val < 12 → E t.mem base i = E s.mem base i := fun i h => by
    rw [ee, vstepEnv_keep _ _ _ _ h]
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
  · rw [ee]; exact vladder_step hn hi.rep hi.q hi.na hi.d
  · rw [pt_congr' (kk 8 (by decide)) (kk 9 (by decide)) (kk 10 (by decide))]; exact hi.q
  · rw [pt_congr' (kk 6 (by decide)) (kk 7 (by decide)) (kk 10 (by decide))]; exact hi.na
  · rw [kk 11 (by decide)]; exact hi.d
  · rw [hz, b₆, show BitVec.ofNat 32 n - (0 : BitVec 32) = BitVec.ofNat 32 n from BitVec.sub_zero _,
      ofNat_beq_zero (by omega)]

theorem vloop_ok {s₀ s : State} {base : Addr} {S K : Nat} {A : Spec.Ed448.Point}
    (hbits : ∀ t < 456, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (pair2 S K t))
    (hi : ∀ s', s'.gpr .esi = BitVec.ofNat 32 456 → (∀ r, r ≠ .esi → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → VInv base S K A s₀ s' 456) :
    WP isa vloop s fun s' => VInv base S K A s₀ s' 0 := by
  unfold vloop
  refine WP.seq (WP.mono (setCounter_ok s 456 (by decide)) fun s' ⟨h1, h2, h3, h4, h5⟩ => ?_)
  refine WP.loop (M := isa) (body := vstep) (c := .ne) (Q := fun s' => VInv base S K A s₀ s' 0)
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 456 ∧ VInv base S K A s₀ s m) ?_ 456 s'
    ⟨by decide, by decide, hi s' h1 h2 h3 h4 h5⟩
  intro m s ⟨h1, h2, hi⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine WP.mono (vstep_ok (by omega) hbits hi) fun s' ⟨hi', hz⟩ => ?_
  simp only [eval, hz, Option.map_some]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, hi'⟩
  · refine .inr ⟨by simp only [decide_eq_false (by omega : ¬m = 0), Bool.not_false], m, by omega,
      by omega, by omega, hi'⟩

end VG.Proof.Ed448.X86

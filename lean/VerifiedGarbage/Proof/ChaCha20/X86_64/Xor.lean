import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Spill
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Impl.ChaCha20.X86_64
import VerifiedGarbage.Proof.ChaCha20.StreamBytes
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.ChaCha20.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Impl.ChaCha20.X86_64.Xor
import VerifiedGarbage.Proof.ChaCha20.X86_64.Lit

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.X86_64.Block`. -/
section

section

/-!
# ChaCha20 block function on x86-64: the rounds
-/

namespace VG.Proof.ChaCha20.X86_64

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64
open VG.Spec.ChaCha20 (Word quarterRound qround innerBlock)
open VG.Proof.ChaCha20

theorem qr_ok {a b c d : Reg} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) (s : State) (va vb vc vd : Word)
    (ha : s.gpr a = va.setWidth 64) (hb : s.gpr b = vb.setWidth 64)
    (hc : s.gpr c = vc.setWidth 64) (hd : s.gpr d = vd.setWidth 64) :
    WP isa (.block (VG.Impl.ChaCha20.X86_64.qr a b c d)) s fun s' =>
      s'.gpr a = (quarterRound va vb vc vd).1.setWidth 64 ∧
      s'.gpr b = (quarterRound va vb vc vd).2.1.setWidth 64 ∧
      s'.gpr c = (quarterRound va vb vc vd).2.2.1.setWidth 64 ∧
      s'.gpr d = (quarterRound va vb vc vd).2.2.2.setWidth 64 ∧
      (∀ r, r ≠ a → r ≠ b → r ≠ c → r ≠ d → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [↓reduceIte, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.reducePow, and_self, and_true, VG.Impl.ChaCha20.X86_64.qr, runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu32, execShift32, readSrc32,
    isa, State.setReg32, State.setReg, arithFlags, State.setFlags, ha, hb, hc, hd,
    hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm, hcd.symm,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  and_intros
  all_goals first
    | simp only [quarterRound_eq]
    | (intro r h1 h2 h3 h4; simp [h1, h2, h3, h4])

/-! ## Where the words are -/

/-- Word `k` is in its register `wreg k` (rather than its slot): words 8 and 9
when `p = false`, words 10 and 11 when `p = true`, and always the others. -/
def inReg (p : Bool) (k : Nat) : Bool :=
  if k = 8 ∨ k = 9 then !p else if k = 10 ∨ k = 11 then p else true

/-- The home slot of word `k` (8–11). -/
abbrev slotAddr (buf : Addr) (k : Nat) : Addr := buf + BitVec.ofInt 64 ((VG.Impl.ChaCha20.X86_64.slotOff k : Nat) : Int)

/-- The state `v` is in the registers and slots of layout `p`. -/
def Holds (buf : Addr) (p : Bool) (v : CState) (s : State) : Prop :=
  ∀ k (hk : k < 16), if VG.Proof.ChaCha20.X86_64.inReg p k then s.gpr (wreg k) = v[k].setWidth 64
    else s.mem.readW (VG.Proof.ChaCha20.X86_64.slotAddr buf k) 32 = v[k]

theorem wreg_ne_rsi (k : Nat) : wreg k ≠ .rsi := by
  unfold wreg; split <;> decide

theorem wreg_ne_rsp (k : Nat) : wreg k ≠ .rsp := by
  unfold wreg; split <;> decide

/-! ## One quarter round -/

/-- The side conditions of `quarter_ok`, decidable for concrete arguments:
the four words are in distinct registers, and no other word in a register
shares one of them. -/
def QSide (p : Bool) (x y z w : Nat) : Bool :=
  VG.Proof.ChaCha20.X86_64.inReg p x && VG.Proof.ChaCha20.X86_64.inReg p y && VG.Proof.ChaCha20.X86_64.inReg p z && VG.Proof.ChaCha20.X86_64.inReg p w && [x, y, z, w].Nodup &&
  [wreg x, wreg y, wreg z, wreg w].Nodup &&
  (List.range 16).all fun k => [x, y, z, w].contains k || !VG.Proof.ChaCha20.X86_64.inReg p k ||
    !([wreg x, wreg y, wreg z, wreg w].contains (wreg k))

theorem quarter_ok {p : Bool} {x y z w : Nat} (hx : x < 16) (hy : y < 16) (hz : z < 16)
    (hw : w < 16) (hq : VG.Proof.ChaCha20.X86_64.QSide p x y z w = true) {buf : Addr} {v : CState} {s : State}
    (h : VG.Proof.ChaCha20.X86_64.Holds buf p v s) :
    WP isa (VG.Impl.ChaCha20.X86_64.quarter x y z w) s fun s' =>
      VG.Proof.ChaCha20.X86_64.Holds buf p (qround v ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ ⟨w, hw⟩) s' ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rsi = s.gpr .rsi ∧ s'.gpr .rsp = s.gpr .rsp := by
  simp only [VG.Proof.ChaCha20.X86_64.QSide, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hq
  obtain ⟨⟨⟨⟨⟨⟨ix, iy⟩, iz⟩, iw⟩, nd⟩, nr⟩, others⟩ := hq
  have nd' : (x ≠ y ∧ x ≠ z ∧ x ≠ w) ∧ (y ≠ z ∧ y ≠ w) ∧ z ≠ w := by simpa using nd
  have nr' : (wreg x ≠ wreg y ∧ wreg x ≠ wreg z ∧ wreg x ≠ wreg w) ∧
      (wreg y ≠ wreg z ∧ wreg y ≠ wreg w) ∧ wreg z ≠ wreg w := by simpa using nr
  obtain ⟨⟨nxy, nxz, nxw⟩, ⟨nyz, nyw⟩, nzw⟩ := nd'
  obtain ⟨⟨rxy, rxz, rxw⟩, ⟨ryz, ryw⟩, rzw⟩ := nr'
  have gx := h x hx; have gy := h y hy; have gz := h z hz; have gw := h w hw
  simp only [ix, iy, iz, iw, ite_true] at gx gy gz gw
  refine WP.mono (VG.Proof.ChaCha20.X86_64.qr_ok rxy rxz rxw ryz ryw rzw s _ _ _ _ gx gy gz gw)
    fun s' ⟨ha, hb, hc, hd, hr, hm, hrd, hwr⟩ => ⟨fun k hk => ?_, hm, hrd, hwr,
      hr _ (VG.Proof.ChaCha20.X86_64.wreg_ne_rsi x).symm (VG.Proof.ChaCha20.X86_64.wreg_ne_rsi y).symm (VG.Proof.ChaCha20.X86_64.wreg_ne_rsi z).symm (VG.Proof.ChaCha20.X86_64.wreg_ne_rsi w).symm,
      hr _ (VG.Proof.ChaCha20.X86_64.wreg_ne_rsp x).symm (VG.Proof.ChaCha20.X86_64.wreg_ne_rsp y).symm (VG.Proof.ChaCha20.X86_64.wreg_ne_rsp z).symm (VG.Proof.ChaCha20.X86_64.wreg_ne_rsp w).symm⟩
  rw [qround_get _ _ _ _ _ k hk]
  simp only
  by_cases ew : w = k
  · subst ew; simp only [iw, ite_true]; exact hd
  by_cases ez : z = k
  · subst ez; simp only [iz, ite_true, ew]; exact hc
  by_cases ey : y = k
  · subst ey; simp only [iy, ite_true, ew, ez]; exact hb
  by_cases ex : x = k
  · subst ex; simp only [ix, ite_true, ew, ez, ey]; exact ha
  simp only [ew, ez, ey, ex, ite_false]
  have hk' := h k hk
  have ho := others k hk
  split
  · rename_i hin
    simp only [hin, ite_true] at hk'
    have ho' : wreg k ≠ wreg x ∧ wreg k ≠ wreg y ∧ wreg k ≠ wreg z ∧ wreg k ≠ wreg w := by
      simpa [Ne.symm ex, Ne.symm ey, Ne.symm ez, Ne.symm ew, hin] using ho
    rw [hr _ ho'.1 ho'.2.1 ho'.2.2.1 ho'.2.2.2]; exact hk'
  · rename_i hin
    simp only [hin] at hk'
    rw [hm]; exact hk'

/-! ## Addresses in `buf` -/

theorem ofInt_natCast (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofInt 64 (d : Int) := rfl

theorem off_sep (p : Addr) {d e n k : Nat} (hd : d < 2 ^ 32) (he : e < 2 ^ 32) (hn : n ≤ 8)
    (hk : k ≤ 8) (h : d + n ≤ e ∨ e + k ≤ d) :
    Mem.Sep (p + BitVec.ofInt 64 (d : Int)) n (p + BitVec.ofInt 64 (e : Int)) k := by
  rw [VG.Proof.ChaCha20.X86_64.ofInt_natCast, VG.Proof.ChaCha20.X86_64.ofInt_natCast]; exact Offset.sep p h (by lit_omega) (by lit_omega)

/-- Reading a 32-bit word after writing a (32- or 64-bit) value elsewhere in `buf`. -/
theorem readW_writeW_off (m : Mem) (p : Addr) {w' : Nat} (v : BitVec w') {d e : Nat}
    (hw' : w' = 32 ∨ w' = 64) (hd : d < 2 ^ 32) (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + w' / 8 ≤ d) :
    (m.writeW (p + BitVec.ofInt 64 (e : Int)) v).readW (p + BitVec.ofInt 64 (d : Int)) 32 =
      m.readW (p + BitVec.ofInt 64 (d : Int)) 32 :=
  Mem.readW_writeW_sep (VG.Proof.ChaCha20.X86_64.off_sep p hd he (by lit_omega) (by lit_omega) h) (by decide)

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem contains_off {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofInt 64 (off : Int)) n := by
  rw [VG.Proof.ChaCha20.X86_64.ofInt_natCast]; exact Offset.contains_base base h ho

/-- The four home slots. -/
abbrev slotR (buf : Addr) : Region := ⟨buf + BitVec.ofInt 64 ((128 : Nat) : Int), 16⟩

/-! ## Swapping the pair of third-row words -/

/-- The rounds invariant, relative to the state `s₀` at the start of the rounds. -/
structure RI (buf : Addr) (p : Bool) (v : CState) (s₀ s : State) : Prop where
  holds : VG.Proof.ChaCha20.X86_64.Holds buf p v s
  frame : Frame [VG.Proof.ChaCha20.X86_64.slotR buf] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsi : s.gpr .rsi = s₀.gpr .rsi
  rsp : s.gpr .rsp = s₀.gpr .rsp

theorem quarter_step {p : Bool} {x y z w : Nat} (hx : x < 16) (hy : y < 16) (hz : z < 16)
    (hw : w < 16) (hq : VG.Proof.ChaCha20.X86_64.QSide p x y z w = true) {buf : Addr} {v : CState} {s₀ s : State}
    (h : VG.Proof.ChaCha20.X86_64.RI buf p v s₀ s) :
    WP isa (VG.Impl.ChaCha20.X86_64.quarter x y z w) s (VG.Proof.ChaCha20.X86_64.RI buf p (qround v ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ ⟨w, hw⟩) s₀) :=
  WP.mono (VG.Proof.ChaCha20.X86_64.quarter_ok hx hy hz hw hq h.holds) fun _ ⟨hh, hm, hrd, hwr, hrsi, hrsp⟩ =>
    ⟨hh, hm ▸ h.frame, hrd.trans h.rd, hwr.trans h.wr, hrsi.trans h.rsi, hrsp.trans h.rsp⟩

abbrev bufR (buf : Addr) : Region := ⟨buf, 256⟩

theorem slotR_contains (buf : Addr) {d : Nat} (h1 : 128 ≤ d) (h2 : d + 4 ≤ 144) :
    (VG.Proof.ChaCha20.X86_64.slotR buf).Contains (buf + BitVec.ofNat 64 d) 4 := by
  rw [VG.Proof.ChaCha20.X86_64.slotR, VG.Proof.ChaCha20.X86_64.ofInt_natCast]; exact Offset.contains buf h1 (by lit_omega) (by lit_omega)

theorem in_buf {rs ws : List Region} {buf : Addr} (hw : VG.Proof.ChaCha20.X86_64.bufR buf ∈ ws) {d n : Nat} (h : d + n ≤ 256) :
    InRegions (rs ++ ws) (buf + BitVec.ofInt 64 (d : Int)) n :=
  ⟨VG.Proof.ChaCha20.X86_64.bufR buf, List.mem_append_right _ hw, VG.Proof.ChaCha20.X86_64.contains_off h (by lit_omega)⟩

theorem out_buf {ws : List Region} {buf : Addr} (hw : VG.Proof.ChaCha20.X86_64.bufR buf ∈ ws) {d n : Nat} (h : d + n ≤ 256) :
    InRegions ws (buf + BitVec.ofInt 64 (d : Int)) n :=
  ⟨VG.Proof.ChaCha20.X86_64.bufR buf, hw, VG.Proof.ChaCha20.X86_64.contains_off h (by lit_omega)⟩

/-- The words after the swap of the third-row words `i, i + 1` (to their slots) and
`j, j + 1` (to `r14, r15`). -/
theorem holds_swap {buf : Addr} {v : CState} {s : State} {p : Bool} {i j : Nat}
    (hij : (p = false ∧ i = 8 ∧ j = 10) ∨ (p = true ∧ i = 10 ∧ j = 8)) (h : VG.Proof.ChaCha20.X86_64.Holds buf p v s) :
    VG.Proof.ChaCha20.X86_64.Holds buf (!p) v { s with
      mem := (s.mem.writeW (VG.Proof.ChaCha20.X86_64.slotAddr buf i) ((s.gpr .r14).setWidth 32)).writeW
        (VG.Proof.ChaCha20.X86_64.slotAddr buf (i + 1)) ((s.gpr .r15).setWidth 32),
      gpr := fun r => if r = .r15 then (((s.mem.writeW (VG.Proof.ChaCha20.X86_64.slotAddr buf i) ((s.gpr .r14).setWidth 32)).writeW
        (VG.Proof.ChaCha20.X86_64.slotAddr buf (i + 1)) ((s.gpr .r15).setWidth 32)).readW (VG.Proof.ChaCha20.X86_64.slotAddr buf (j + 1)) 32).setWidth 64
        else if r = .r14 then (((s.mem.writeW (VG.Proof.ChaCha20.X86_64.slotAddr buf i) ((s.gpr .r14).setWidth 32)).writeW
        (VG.Proof.ChaCha20.X86_64.slotAddr buf (i + 1)) ((s.gpr .r15).setWidth 32)).readW (VG.Proof.ChaCha20.X86_64.slotAddr buf j) 32).setWidth 64
        else s.gpr r } := by
  intro k hk
  have hk' := h k hk
  have rd : ∀ (m : Mem) {d e : Nat} (w : BitVec 32), 8 ≤ d → d ≤ 11 → 8 ≤ e → e ≤ 11 → d ≠ e →
      (m.writeW (VG.Proof.ChaCha20.X86_64.slotAddr buf e) w).readW (VG.Proof.ChaCha20.X86_64.slotAddr buf d) 32 = m.readW (VG.Proof.ChaCha20.X86_64.slotAddr buf d) 32 :=
    fun m d e w h1 h2 h3 h4 hde => VG.Proof.ChaCha20.X86_64.readW_writeW_off m buf w (.inl rfl)
      (by simp only [VG.Impl.ChaCha20.X86_64.slotOff]; omega) (by simp only [VG.Impl.ChaCha20.X86_64.slotOff]; omega) (by simp only [VG.Impl.ChaCha20.X86_64.slotOff]; omega)
  by_cases hs : 8 ≤ k ∧ k ≤ 11
  · have hk4 : k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 := by omega
    rcases hij with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    rcases hk4 with rfl | rfl | rfl | rfl <;>
    simp only [VG.Proof.ChaCha20.X86_64.inReg, wreg, Nat.reduceAdd, Nat.reduceEqDiff, or_true, or_false,
      ↓reduceIte, reduceCtorEq, Bool.not_false, Bool.not_true, Bool.false_eq_true] at hk' ⊢ <;>
    simp (disch := omega) only [rd, Mem.readW_writeW_self32, hk', BitVec.setWidth_setWidth_of_le,
      BitVec.setWidth_eq]
  · have e1 : ¬(k = 8 ∨ k = 9) := by omega
    have e2 : ¬(k = 10 ∨ k = 11) := by omega
    have hr : VG.Proof.ChaCha20.X86_64.inReg (!p) k = VG.Proof.ChaCha20.X86_64.inReg p k := by simp only [VG.Proof.ChaCha20.X86_64.inReg, e1, e2, ite_false]
    have hw : wreg k ≠ .r14 ∧ wreg k ≠ .r15 :=
      (show ∀ k < 16, ¬(8 ≤ k ∧ k ≤ 11) → wreg k ≠ .r14 ∧ wreg k ≠ .r15 by decide) k hk hs
    have hin : VG.Proof.ChaCha20.X86_64.inReg p k = true := by simp only [VG.Proof.ChaCha20.X86_64.inReg, e1, e2, ite_false]
    simp only [hr, hin, ite_true] at hk' ⊢
    simp only [hw.1, hw.2, ite_false]; exact hk'

theorem swap_step {p : Bool} {buf : Addr} {v : CState} {s₀ s : State} (h : VG.Proof.ChaCha20.X86_64.RI buf p v s₀ s)
    (hbuf : s₀.gpr .rsi = buf) (hw : VG.Proof.ChaCha20.X86_64.bufR buf ∈ s₀.wr) :
    WP isa (VG.Impl.ChaCha20.X86_64.swap (if p then 10 else 8) (if p then 8 else 10)) s (VG.Proof.ChaCha20.X86_64.RI buf (!p) v s₀) := by
  have hrsi : s.gpr .rsi = buf := h.rsi.trans hbuf
  have hw' : VG.Proof.ChaCha20.X86_64.bufR buf ∈ s.wr := h.wr ▸ hw
  have i8 : InRegions (s.rd ++ s.wr) (VG.Proof.ChaCha20.X86_64.slotAddr buf 8) 4 := VG.Proof.ChaCha20.X86_64.in_buf hw' (by decide)
  have i9 : InRegions (s.rd ++ s.wr) (VG.Proof.ChaCha20.X86_64.slotAddr buf 9) 4 := VG.Proof.ChaCha20.X86_64.in_buf hw' (by decide)
  have i10 : InRegions (s.rd ++ s.wr) (VG.Proof.ChaCha20.X86_64.slotAddr buf 10) 4 := VG.Proof.ChaCha20.X86_64.in_buf hw' (by decide)
  have i11 : InRegions (s.rd ++ s.wr) (VG.Proof.ChaCha20.X86_64.slotAddr buf 11) 4 := VG.Proof.ChaCha20.X86_64.in_buf hw' (by decide)
  have o8 : InRegions s.wr (VG.Proof.ChaCha20.X86_64.slotAddr buf 8) 4 := VG.Proof.ChaCha20.X86_64.out_buf hw' (by decide)
  have o9 : InRegions s.wr (VG.Proof.ChaCha20.X86_64.slotAddr buf 9) 4 := VG.Proof.ChaCha20.X86_64.out_buf hw' (by decide)
  have o10 : InRegions s.wr (VG.Proof.ChaCha20.X86_64.slotAddr buf 10) 4 := VG.Proof.ChaCha20.X86_64.out_buf hw' (by decide)
  have o11 : InRegions s.wr (VG.Proof.ChaCha20.X86_64.slotAddr buf 11) 4 := VG.Proof.ChaCha20.X86_64.out_buf hw' (by decide)
  have hf₁ := h.frame
  cases p
  · apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, Bool.not_false, Nat.reduceAdd, runBlock_cons, runStep_some, runBlock_nil,
      exec, readSrc32, isa, VG.Proof.ChaCha20.X86_64.ea_at, State.load32, State.store32, State.setReg32, State.setReg, i10, i11, o8,
      o9, hrsi, Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨VG.Proof.ChaCha20.X86_64.holds_swap (.inl ⟨rfl, rfl, rfl⟩) h.holds, ?_, h.rd, h.wr, by simp [h.rsi], by simp [h.rsp]⟩
    exact (hf₁.writeW (List.mem_singleton_self _) _
      (VG.Proof.ChaCha20.X86_64.slotR_contains buf (d := 128) (by lit_omega) (by lit_omega))).writeW
      (List.mem_singleton_self _) _ (VG.Proof.ChaCha20.X86_64.slotR_contains buf (d := 132) (by lit_omega) (by lit_omega))
  · apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, Bool.not_true, Nat.reduceAdd, runBlock_cons, runStep_some, runBlock_nil,
      exec, readSrc32, isa, VG.Proof.ChaCha20.X86_64.ea_at, State.load32, State.store32, State.setReg32, State.setReg, i8, i9, o10,
      o11, hrsi, Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨VG.Proof.ChaCha20.X86_64.holds_swap (.inr ⟨rfl, rfl, rfl⟩) h.holds, ?_, h.rd, h.wr, by simp [h.rsi], by simp [h.rsp]⟩
    exact (hf₁.writeW (List.mem_singleton_self _) _
      (VG.Proof.ChaCha20.X86_64.slotR_contains buf (d := 136) (by lit_omega) (by lit_omega))).writeW
      (List.mem_singleton_self _) _ (VG.Proof.ChaCha20.X86_64.slotR_contains buf (d := 140) (by lit_omega) (by lit_omega))

/-! ## Double rounds -/

theorem doubleRound_ok {buf : Addr} {v : CState} {s₀ s : State} (h : VG.Proof.ChaCha20.X86_64.RI buf false v s₀ s)
    (hbuf : s₀.gpr .rsi = buf) (hw : VG.Proof.ChaCha20.X86_64.bufR buf ∈ s₀.wr) :
    WP isa VG.Impl.ChaCha20.X86_64.doubleRound s (VG.Proof.ChaCha20.X86_64.RI buf false (innerBlock v) s₀) := by
  unfold VG.Impl.ChaCha20.X86_64.doubleRound
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86_64.quarter_step (x := 0) (y := 4) (z := 8) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) h) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86_64.quarter_step (x := 1) (y := 5) (z := 9) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86_64.swap_step (p := false) h₂ hbuf hw) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86_64.quarter_step (x := 2) (y := 6) (z := 10) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86_64.quarter_step (x := 3) (y := 7) (z := 11) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86_64.quarter_step (x := 0) (y := 5) (z := 10) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₅) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86_64.quarter_step (x := 1) (y := 6) (z := 11) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₆) fun s₇ h₇ => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86_64.swap_step (p := true) h₇ hbuf hw) fun s₈ h₈ => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86_64.quarter_step (x := 2) (y := 7) (z := 8) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₈) fun s₉ h₉ => ?_)
  exact WP.mono (VG.Proof.ChaCha20.X86_64.quarter_step (x := 3) (y := 4) (z := 9) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₉) fun _ h => h

theorem rounds_ok {buf : Addr} {v : CState} {s₀ : State} (h : VG.Proof.ChaCha20.X86_64.Holds buf false v s₀)
    (hbuf : s₀.gpr .rsi = buf) (hw : VG.Proof.ChaCha20.X86_64.bufR buf ∈ s₀.wr) :
    ∀ n, WP isa (VG.Impl.ChaCha20.X86_64.rounds n) s₀ (VG.Proof.ChaCha20.X86_64.RI buf false (Nat.repeat innerBlock n v) s₀)
  | 0 => WP.block_nil ⟨h, Frame.refl _ _, rfl, rfl, rfl, rfl⟩
  | n + 1 => WP.seq (WP.mono (VG.Proof.ChaCha20.X86_64.rounds_ok h hbuf hw n) fun _ h' => VG.Proof.ChaCha20.X86_64.doubleRound_ok h' hbuf hw)

end VG.Proof.ChaCha20.X86_64

end

/-!
# ChaCha20 block function on x86-64: the whole function
-/

namespace VG.Proof.ChaCha20

open Spec.ChaCha20 VG.X86_64

/-- X86-64 contract for `vg_chacha20_block(state: *const [u32; 16], buf: *mut
[u32; 64])`: writes `block` of the state at `state` to the first 16 words of
`buf`.

The code may read `state` (64 bytes) and read and write `buf` (256 bytes; its
first 64 bytes hold the result on exit, and the rest is scratch space whose
contents on exit are unspecified). `buf` may not overlap `state` or the
return address on the stack. The pointers are public; the state (key,
counter and nonce) is secret. -/
def blockX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 64⟩
    let buf : Region := ⟨s.gpr .rsi, 256⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [state] ∧ s.wr = [buf] ∧ buf.Disjoint state ∧ ret.Disjoint buf
  post s s' := stateAt s'.mem (s.gpr .rsi) = block (stateAt s.mem (s.gpr .rdi))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi

end VG.Proof.ChaCha20

namespace VG.Proof.ChaCha20.X86_64

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64
open VG.Spec.ChaCha20 (Word stateAt innerBlock)

/-- An address `buf + d` as the code computes it. -/
abbrev bufAt (buf : Addr) (d : Nat) : Addr := buf + BitVec.ofInt 64 (d : Int)

theorem in_lt {k : Nat} (hk : k < 16) : inOff k + 4 ≤ 256 := by simp only [inOff]; omega
theorem out_lt {k : Nat} (hk : k < 16) : outOff k + 4 ≤ 256 := by simp only [outOff]; omega

/-! ## Copying the state -/

theorem copyWord_ok {k : Nat} (hk : k < 16) {s : State} {st buf : Addr} (hrdi : s.gpr .rdi = st)
    (hrsi : s.gpr .rsi = buf) (hin : InRegions (s.rd ++ s.wr) (VG.Proof.ChaCha20.X86_64.bufAt st (4 * k)) 4)
    (hw : VG.Proof.ChaCha20.X86_64.bufR buf ∈ s.wr) :
    WP isa (.block (copyWord k)) s fun s' =>
      s'.mem = (if k = 10 ∨ k = 11 then
          (s.mem.writeW (VG.Proof.ChaCha20.X86_64.bufAt buf (inOff k)) (s.mem.readW (VG.Proof.ChaCha20.X86_64.bufAt st (4 * k)) 32)).writeW
            (VG.Proof.ChaCha20.X86_64.bufAt buf (VG.Impl.ChaCha20.X86_64.slotOff k)) (s.mem.readW (VG.Proof.ChaCha20.X86_64.bufAt st (4 * k)) 32)
        else s.mem.writeW (VG.Proof.ChaCha20.X86_64.bufAt buf (inOff k)) (s.mem.readW (VG.Proof.ChaCha20.X86_64.bufAt st (4 * k)) 32)) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have o₁ := VG.Proof.ChaCha20.X86_64.out_buf hw (d := inOff k) (n := 4) (VG.Proof.ChaCha20.X86_64.in_lt hk)
  apply WP.of_runBlock
  by_cases h : k = 10 ∨ k = 11
  · have o₂ := VG.Proof.ChaCha20.X86_64.out_buf hw (d := VG.Impl.ChaCha20.X86_64.slotOff k) (n := 4) (by simp only [VG.Impl.ChaCha20.X86_64.slotOff]; omega)
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, and_self, copyWord, h, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
          exec, readSrc32, isa, VG.Proof.ChaCha20.X86_64.ea_at, State.load32, State.store32,
      State.setReg32, State.setReg, hrdi, hin, hrsi, o₁, o₂, BitVec.setWidth_setWidth_of_le,
      BitVec.setWidth_eq, Option.map_some, Option.some.injEq, exists_eq_left']
    exact ⟨trivial, fun r hr => by simp [hr], trivial⟩
  · simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, and_self, copyWord, h, List.append_nil,
      runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32,
          isa, VG.Proof.ChaCha20.X86_64.ea_at, State.load32, State.store32, State.setReg32,
      State.setReg, hrdi, hin, hrsi, o₁, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
      Option.map_some, Option.some.injEq, exists_eq_left']
    exact ⟨trivial, fun r hr => by simp [hr], trivial⟩

/-! ## Offsets -/

/-- A sub-range `[a, a + len)` of `buf` contains `[d, d + n)`. -/
theorem contains_sub (p : Addr) {a len d n : Nat} (h1 : a ≤ d) (h2 : d + n ≤ a + len)
    (h3 : a + len < 2 ^ 32) :
    (⟨VG.Proof.ChaCha20.X86_64.bufAt p a, len⟩ : Region).Contains (VG.Proof.ChaCha20.X86_64.bufAt p d) n := by
  simp only [VG.Proof.ChaCha20.X86_64.bufAt, VG.Proof.ChaCha20.X86_64.ofInt_natCast]; exact Offset.contains p h1 h2 (by lit_omega)

/-- Two sub-ranges of `buf` that do not overlap. -/
theorem disjoint_sub (p : Addr) {a la b lb : Nat} (h : a + la ≤ b ∨ b + lb ≤ a)
    (ha : a + la < 2 ^ 32) (hb : b + lb < 2 ^ 32) :
    (⟨VG.Proof.ChaCha20.X86_64.bufAt p a, la⟩ : Region).Disjoint ⟨VG.Proof.ChaCha20.X86_64.bufAt p b, lb⟩ := by
  simp only [VG.Proof.ChaCha20.X86_64.bufAt, VG.Proof.ChaCha20.X86_64.ofInt_natCast]; exact Offset.disjoint p h (by lit_omega) (by lit_omega)

/-- A sub-range of `buf` is inside `buf`. -/
theorem sub_buf (p : Addr) {a len : Nat} (h : a + len ≤ 256) :
    Region.Sub ⟨VG.Proof.ChaCha20.X86_64.bufAt p a, len⟩ (VG.Proof.ChaCha20.X86_64.bufR p) := by
  simp only [VG.Proof.ChaCha20.X86_64.bufAt, VG.Proof.ChaCha20.X86_64.ofInt_natCast]; exact Offset.sub_base p h

/-- The output area of `buf`. -/
abbrev outR (p : Addr) : Region := ⟨VG.Proof.ChaCha20.X86_64.bufAt p 0, 64⟩
/-- Everything in `buf` but the saved registers: output, input copy and slots. -/
abbrev workR (p : Addr) : Region := ⟨VG.Proof.ChaCha20.X86_64.bufAt p 0, 144⟩

theorem sub_work (p : Addr) {a len : Nat} (h : a + len ≤ 144) :
    Region.Sub ⟨VG.Proof.ChaCha20.X86_64.bufAt p a, len⟩ (VG.Proof.ChaCha20.X86_64.workR p) := by
  simp only [VG.Proof.ChaCha20.X86_64.workR, VG.Proof.ChaCha20.X86_64.bufAt, VG.Proof.ChaCha20.X86_64.ofInt_natCast]; exact Offset.sub p (by lit_omega) (by lit_omega)

theorem frame_work {p : Addr} {a len : Nat} (h : a + len ≤ 144) {m m' : Mem}
    (hf : Frame [⟨VG.Proof.ChaCha20.X86_64.bufAt p a, len⟩] m m') : Frame [VG.Proof.ChaCha20.X86_64.workR p] m m' :=
  hf.sub fun r hr => ⟨VG.Proof.ChaCha20.X86_64.workR p, List.mem_singleton_self _, by
    simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.ChaCha20.X86_64.sub_work p h⟩

/-! ## The precondition -/

section
variable (s₀ : State)
abbrev st : Addr := s₀.gpr .rdi
abbrev buf : Addr := s₀.gpr .rsi
abbrev stR : Region := ⟨VG.Proof.ChaCha20.X86_64.st s₀, 64⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
/-- The input state. -/
abbrev V : CState := stateAt s₀.mem (VG.Proof.ChaCha20.X86_64.st s₀)
end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.ChaCha20.X86_64.stR s₀]
  wr : s₀.wr = [VG.Proof.ChaCha20.X86_64.bufR (VG.Proof.ChaCha20.X86_64.buf s₀)]
  buf_st : (VG.Proof.ChaCha20.X86_64.bufR (VG.Proof.ChaCha20.X86_64.buf s₀)).Disjoint (VG.Proof.ChaCha20.X86_64.stR s₀)
  ret_buf : (VG.Proof.ChaCha20.X86_64.retR s₀).Disjoint (VG.Proof.ChaCha20.X86_64.bufR (VG.Proof.ChaCha20.X86_64.buf s₀))

theorem pre_of (s₀ : State) (h : Proof.ChaCha20.blockX86_64.pre s₀) : VG.Proof.ChaCha20.X86_64.Pre s₀ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem Pre.hw {s₀ : State} (hp : VG.Proof.ChaCha20.X86_64.Pre s₀) : VG.Proof.ChaCha20.X86_64.bufR (VG.Proof.ChaCha20.X86_64.buf s₀) ∈ s₀.wr := by simp [hp.wr]

theorem Pre.in_st {s₀ : State} (hp : VG.Proof.ChaCha20.X86_64.Pre s₀) {k : Nat} (hk : k < 16) (ws : List Region) :
    InRegions (s₀.rd ++ ws) (VG.Proof.ChaCha20.X86_64.bufAt (VG.Proof.ChaCha20.X86_64.st s₀) (4 * k)) 4 :=
  ⟨VG.Proof.ChaCha20.X86_64.stR s₀, by simp [hp.rd], VG.Proof.ChaCha20.X86_64.contains_off (by lit_omega) (by lit_omega)⟩

theorem V_get (s₀ : State) {k : Nat} (hk : k < 16) :
    (VG.Proof.ChaCha20.X86_64.V s₀)[k] = s₀.mem.readW (VG.Proof.ChaCha20.X86_64.bufAt (VG.Proof.ChaCha20.X86_64.st s₀) (4 * k)) 32 := by
  simp only [VG.Proof.ChaCha20.X86_64.V, stateAt, Vector.getElem_ofFn, VG.Proof.ChaCha20.X86_64.bufAt, VG.Proof.ChaCha20.X86_64.ofInt_natCast]

/-- Reading the input state after writes to `buf` only. -/
theorem read_st {s₀ : State} (hp : VG.Proof.ChaCha20.X86_64.Pre s₀) {m : Mem} (hf : Frame [VG.Proof.ChaCha20.X86_64.bufR (VG.Proof.ChaCha20.X86_64.buf s₀)] s₀.mem m)
    {k : Nat} (hk : k < 16) : m.readW (VG.Proof.ChaCha20.X86_64.bufAt (VG.Proof.ChaCha20.X86_64.st s₀) (4 * k)) 32 = (VG.Proof.ChaCha20.X86_64.V s₀)[k] := by
  rw [VG.Proof.ChaCha20.X86_64.V_get _ hk]
  exact hf.readW (r := VG.Proof.ChaCha20.X86_64.stR s₀) (VG.Proof.ChaCha20.X86_64.contains_off (by lit_omega) (by lit_omega))
    (by simpa using hp.buf_st.symm) (by decide)

/-! ## Phase 2: copying the state -/

/-- The copy invariant after `n` words, relative to the state `s₁` after the prologue's stores. -/
structure CI (s₀ s₁ : State) (n : Nat) (s : State) : Prop where
  gpr : ∀ r, r ≠ .rax → s.gpr r = s₁.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨VG.Proof.ChaCha20.X86_64.bufAt (VG.Proof.ChaCha20.X86_64.buf s₀) 64, 80⟩] s₁.mem s.mem
  inw : ∀ j (hj : j < 16), j < n → s.mem.readW (VG.Proof.ChaCha20.X86_64.bufAt (VG.Proof.ChaCha20.X86_64.buf s₀) (inOff j)) 32 = (VG.Proof.ChaCha20.X86_64.V s₀)[j]
  slot : ∀ j (hj : j < 16), j < n → (j = 10 ∨ j = 11) →
    s.mem.readW (VG.Proof.ChaCha20.X86_64.bufAt (VG.Proof.ChaCha20.X86_64.buf s₀) (VG.Impl.ChaCha20.X86_64.slotOff j)) 32 = (VG.Proof.ChaCha20.X86_64.V s₀)[j]

theorem copy_step {s₀ s₁ : State} (hp : VG.Proof.ChaCha20.X86_64.Pre s₀) (h₁ : s₁.gpr = s₀.gpr)
    (hf₁ : Frame [VG.Proof.ChaCha20.X86_64.bufR (VG.Proof.ChaCha20.X86_64.buf s₀)] s₀.mem s₁.mem) {n : Nat} (hn : n < 16)
    {s : State} (hc : VG.Proof.ChaCha20.X86_64.CI s₀ s₁ n s) : WP isa (.block (copyWord n)) s (VG.Proof.ChaCha20.X86_64.CI s₀ s₁ (n + 1)) := by
  have hrdi : s.gpr .rdi = VG.Proof.ChaCha20.X86_64.st s₀ := by rw [hc.gpr _ (by decide), h₁]
  have hrsi : s.gpr .rsi = VG.Proof.ChaCha20.X86_64.buf s₀ := by rw [hc.gpr _ (by decide), h₁]
  have hfs : Frame [VG.Proof.ChaCha20.X86_64.bufR (VG.Proof.ChaCha20.X86_64.buf s₀)] s₀.mem s.mem :=
    hf₁.trans (hc.frame.sub fun r hr => ⟨VG.Proof.ChaCha20.X86_64.bufR (VG.Proof.ChaCha20.X86_64.buf s₀), List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.ChaCha20.X86_64.sub_buf _ (by lit_omega)⟩)
  refine WP.mono (VG.Proof.ChaCha20.X86_64.copyWord_ok hn hrdi hrsi (by rw [hc.rd, hc.wr]; exact hp.in_st hn _)
    (by rw [hc.wr]; exact hp.hw)) fun s' ⟨hm, hg, hrd, hwr⟩ => ?_
  have hx : s.mem.readW (VG.Proof.ChaCha20.X86_64.bufAt (VG.Proof.ChaCha20.X86_64.st s₀) (4 * n)) 32 = (VG.Proof.ChaCha20.X86_64.V s₀)[n] := VG.Proof.ChaCha20.X86_64.read_st hp hfs hn
  have cin : (⟨VG.Proof.ChaCha20.X86_64.bufAt (VG.Proof.ChaCha20.X86_64.buf s₀) 64, 80⟩ : Region).Contains (VG.Proof.ChaCha20.X86_64.bufAt (VG.Proof.ChaCha20.X86_64.buf s₀) (inOff n)) (32 / 8) :=
    VG.Proof.ChaCha20.X86_64.contains_sub _ (by simp [inOff]) (by simp [inOff]; omega) (by lit_omega)
  refine ⟨fun r hr => (hg r hr).trans (hc.gpr r hr), hrd.trans hc.rd, hwr.trans hc.wr, ?_, ?_, ?_⟩
  · rw [hm]
    split
    · exact (hc.frame.writeW (List.mem_singleton_self _) _ cin).writeW (List.mem_singleton_self _) _
        (VG.Proof.ChaCha20.X86_64.contains_sub _ (by simp [VG.Impl.ChaCha20.X86_64.slotOff]; omega) (by simp [VG.Impl.ChaCha20.X86_64.slotOff]; omega) (by lit_omega))
    · exact hc.frame.writeW (List.mem_singleton_self _) _ cin
  · intro j hj hjn
    rw [hm]
    have e1 : ∀ m : Mem, (m.writeW (VG.Proof.ChaCha20.X86_64.bufAt (VG.Proof.ChaCha20.X86_64.buf s₀) (VG.Impl.ChaCha20.X86_64.slotOff n)) ((VG.Proof.ChaCha20.X86_64.V s₀)[n])).readW
        (VG.Proof.ChaCha20.X86_64.bufAt (VG.Proof.ChaCha20.X86_64.buf s₀) (inOff j)) 32 = m.readW (VG.Proof.ChaCha20.X86_64.bufAt (VG.Proof.ChaCha20.X86_64.buf s₀) (inOff j)) 32 := fun m =>
      VG.Proof.ChaCha20.X86_64.readW_writeW_off m _ _ (by lit_omega) (by simp [inOff]; omega) (by simp [VG.Impl.ChaCha20.X86_64.slotOff]; omega)
        (by simp [inOff, VG.Impl.ChaCha20.X86_64.slotOff]; omega)
    rcases Nat.lt_succ_iff_lt_or_eq.mp hjn with hjn | rfl
    · have e2 : (s.mem.writeW (VG.Proof.ChaCha20.X86_64.bufAt (VG.Proof.ChaCha20.X86_64.buf s₀) (inOff n)) ((VG.Proof.ChaCha20.X86_64.V s₀)[n])).readW
          (VG.Proof.ChaCha20.X86_64.bufAt (VG.Proof.ChaCha20.X86_64.buf s₀) (inOff j)) 32 = s.mem.readW (VG.Proof.ChaCha20.X86_64.bufAt (VG.Proof.ChaCha20.X86_64.buf s₀) (inOff j)) 32 :=
        VG.Proof.ChaCha20.X86_64.readW_writeW_off _ _ _ (by lit_omega) (by simp [inOff]; omega) (by simp [inOff]; omega)
          (by simp [inOff]; omega)
      rw [hx]; split <;> simp only [e1, e2, hc.inw j hj hjn]
    · rw [hx]; split <;> simp only [e1, Mem.readW_writeW_self32]
  · intro j hj hjn h1011
    rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hjn with hjn | rfl
    · have e2 : ∀ m : Mem, ∀ d, d = inOff n ∨ d = VG.Impl.ChaCha20.X86_64.slotOff n → (m.writeW (VG.Proof.ChaCha20.X86_64.bufAt (VG.Proof.ChaCha20.X86_64.buf s₀) d)
          ((VG.Proof.ChaCha20.X86_64.V s₀)[n])).readW (VG.Proof.ChaCha20.X86_64.bufAt (VG.Proof.ChaCha20.X86_64.buf s₀) (VG.Impl.ChaCha20.X86_64.slotOff j)) 32 = m.readW (VG.Proof.ChaCha20.X86_64.bufAt (VG.Proof.ChaCha20.X86_64.buf s₀) (VG.Impl.ChaCha20.X86_64.slotOff j)) 32 := by
        rintro m d (rfl | rfl)
        · exact VG.Proof.ChaCha20.X86_64.readW_writeW_off _ _ _ (by lit_omega) (by simp [VG.Impl.ChaCha20.X86_64.slotOff]; omega) (by simp [inOff]; omega)
            (by simp [inOff, VG.Impl.ChaCha20.X86_64.slotOff]; omega)
        · exact VG.Proof.ChaCha20.X86_64.readW_writeW_off _ _ _ (by lit_omega) (by simp [VG.Impl.ChaCha20.X86_64.slotOff]; omega) (by simp [VG.Impl.ChaCha20.X86_64.slotOff]; omega)
            (by simp [VG.Impl.ChaCha20.X86_64.slotOff]; omega)
      rw [hx]; split <;> simp only [e2 _ _ (.inl rfl), e2 _ _ (.inr rfl), hc.slot j hj hjn h1011]
    · simp only [hx, h1011, ite_true, Mem.readW_writeW_self32]

/-! ## Phase 5: storing the rounds' result -/

/-- The store invariant after `n` words: the result `R` is in the output for
words `< n`, and still in the registers and slots for the others. -/
structure SI (p : Addr) (R : CState) (sB : State) (n : Nat) (s : State) : Prop where
  out : ∀ j (hj : j < 16), j < n → s.mem.readW (VG.Proof.ChaCha20.X86_64.bufAt p (outOff j)) 32 = R[j]
  rest : ∀ j (hj : j < 16), n ≤ j → if VG.Proof.ChaCha20.X86_64.inReg false j then s.gpr (wreg j) = R[j].setWidth 64
    else s.mem.readW (VG.Proof.ChaCha20.X86_64.slotAddr p j) 32 = R[j]
  frame : Frame [VG.Proof.ChaCha20.X86_64.outR p] sB.mem s.mem
  rsi : s.gpr .rsi = p
  rsp : s.gpr .rsp = sB.gpr .rsp
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr

theorem wreg_ne_rax {j : Nat} (h : 11 ≤ j) (hj : j < 16) : wreg j ≠ .rax :=
  (show ∀ j < 16, 11 ≤ j → wreg j ≠ .rax by decide) j hj h

theorem store_step {p : Addr} {R : CState} {sB : State} (hw : VG.Proof.ChaCha20.X86_64.bufR p ∈ sB.wr) {n : Nat} (hn : n < 16)
    {s : State} (hs : VG.Proof.ChaCha20.X86_64.SI p R sB n s) : WP isa (.block (storeWord n)) s (VG.Proof.ChaCha20.X86_64.SI p R sB (n + 1)) := by
  have hw' : VG.Proof.ChaCha20.X86_64.bufR p ∈ s.wr := hs.wr ▸ hw
  have o := VG.Proof.ChaCha20.X86_64.out_buf hw' (d := outOff n) (n := 4) (VG.Proof.ChaCha20.X86_64.out_lt hn)
  have cout : (VG.Proof.ChaCha20.X86_64.outR p).Contains (VG.Proof.ChaCha20.X86_64.bufAt p (outOff n)) (32 / 8) :=
    VG.Proof.ChaCha20.X86_64.contains_sub _ (by lit_omega) (by simp [outOff]; omega) (by lit_omega)
  have hr := hs.rest n hn (Nat.le_refl _)
  have hrsi := hs.rsi
  /- The new memory is the old one with `R[n]` written to output word `n`. -/
  suffices key : ∀ s', s'.mem = s.mem.writeW (VG.Proof.ChaCha20.X86_64.bufAt p (outOff n)) R[n] →
      (∀ j (hj : j < 16), n < j → VG.Proof.ChaCha20.X86_64.inReg false j = true → s'.gpr (wreg j) = s.gpr (wreg j)) →
      s'.gpr .rsi = s.gpr .rsi → s'.gpr .rsp = s.gpr .rsp → s'.rd = s.rd → s'.wr = s.wr →
      VG.Proof.ChaCha20.X86_64.SI p R sB (n + 1) s' by
    apply WP.of_runBlock
    by_cases h : n = 10 ∨ n = 11
    · have hin : VG.Proof.ChaCha20.X86_64.inReg false n = false := by rcases h with rfl | rfl <;> rfl
      simp only [hin, Bool.false_eq_true, ite_false] at hr
      have i := VG.Proof.ChaCha20.X86_64.in_buf (rs := s.rd) hw' (d := VG.Impl.ChaCha20.X86_64.slotOff n) (n := 4) (by simp only [VG.Impl.ChaCha20.X86_64.slotOff]; omega)
      simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, storeWord, h, runBlock_cons,
        runStep_some, runBlock_nil, exec, readSrc32,
        isa, VG.Proof.ChaCha20.X86_64.ea_at, State.load32, State.store32, State.setReg32, State.setReg, hrsi, i, o,
        BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
        Option.map_some, Option.some.injEq, exists_eq_left']
      simp only [VG.Proof.ChaCha20.X86_64.slotAddr] at hr
      refine key _ (by simp only [hr]) (fun j hj hnj _ => ?_) (by simp) (by simp) rfl rfl
      simp [VG.Proof.ChaCha20.X86_64.wreg_ne_rax (show 11 ≤ j by omega) hj]
    · have hin : VG.Proof.ChaCha20.X86_64.inReg false n = true := by
        simp only [VG.Proof.ChaCha20.X86_64.inReg]; split <;> simp_all
      simp only [hin, ite_true] at hr
      simp only [↓reduceIte, Nat.reduceLeDiff, storeWord, h, runBlock_cons,
        runStep_some, runBlock_nil, exec, isa, VG.Proof.ChaCha20.X86_64.ea_at,
        State.store32, hrsi, o, hr, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
        Option.some.injEq, exists_eq_left']
      exact key _ rfl (fun _ _ _ _ => rfl) rfl rfl rfl rfl
  intro s' hm hg hrsi' hrsp' hrd hwr
  refine ⟨fun j hj hjn => ?_, fun j hj hjn => ?_, ?_, hrsi'.trans hs.rsi, hrsp'.trans hs.rsp,
    hrd.trans hs.rd, hwr.trans hs.wr⟩
  · rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hjn with hjn | rfl
    · rw [VG.Proof.ChaCha20.X86_64.readW_writeW_off _ _ _ (by lit_omega) (by simp [outOff]; omega) (by simp [outOff]; omega)
        (by simp [outOff]; omega)]
      exact hs.out j hj hjn
    · exact Mem.readW_writeW_self32 _ _ _
  · have hr' := hs.rest j hj (by lit_omega)
    split
    · rename_i hin; simp only [hin, ite_true] at hr'; rw [hg j hj (by lit_omega) hin]; exact hr'
    · rename_i hin; simp only [hin] at hr'
      rw [hm, VG.Proof.ChaCha20.X86_64.slotAddr, VG.Proof.ChaCha20.X86_64.readW_writeW_off _ _ _ (by lit_omega) (by simp [VG.Impl.ChaCha20.X86_64.slotOff]; omega)
        (by simp [outOff]; omega) (by simp [outOff, VG.Impl.ChaCha20.X86_64.slotOff]; omega)]
      exact hr'
  · rw [hm]; exact hs.frame.writeW (List.mem_singleton_self _) _ cout

/-! ## Phase 6: adding the input state -/

/-- The add invariant after `n` words. -/
structure AI (p : Addr) (R v : CState) (sB : State) (n : Nat) (s : State) : Prop where
  out : ∀ j (hj : j < 16), s.mem.readW (VG.Proof.ChaCha20.X86_64.bufAt p (outOff j)) 32 = if j < n then R[j] + v[j] else R[j]
  inw : ∀ j (hj : j < 16), s.mem.readW (VG.Proof.ChaCha20.X86_64.bufAt p (inOff j)) 32 = v[j]
  frame : Frame [VG.Proof.ChaCha20.X86_64.outR p] sB.mem s.mem
  rsi : s.gpr .rsi = p
  rsp : s.gpr .rsp = sB.gpr .rsp
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr

theorem add_step {p : Addr} {R v : CState} {sB : State} (hw : VG.Proof.ChaCha20.X86_64.bufR p ∈ sB.wr) {n : Nat} (hn : n < 16)
    {s : State} (hs : VG.Proof.ChaCha20.X86_64.AI p R v sB n s) : WP isa (.block (addWord n)) s (VG.Proof.ChaCha20.X86_64.AI p R v sB (n + 1)) := by
  have hw' : VG.Proof.ChaCha20.X86_64.bufR p ∈ s.wr := hs.wr ▸ hw
  have o := VG.Proof.ChaCha20.X86_64.out_buf hw' (d := outOff n) (n := 4) (VG.Proof.ChaCha20.X86_64.out_lt hn)
  have io := VG.Proof.ChaCha20.X86_64.in_buf (rs := s.rd) hw' (d := outOff n) (n := 4) (VG.Proof.ChaCha20.X86_64.out_lt hn)
  have ii := VG.Proof.ChaCha20.X86_64.in_buf (rs := s.rd) hw' (d := inOff n) (n := 4) (VG.Proof.ChaCha20.X86_64.in_lt hn)
  have cout : (VG.Proof.ChaCha20.X86_64.outR p).Contains (VG.Proof.ChaCha20.X86_64.bufAt p (outOff n)) (32 / 8) :=
    VG.Proof.ChaCha20.X86_64.contains_sub _ (by lit_omega) (by simp [outOff]; omega) (by lit_omega)
  have ho := hs.out n hn
  simp only [Nat.lt_irrefl, ite_false] at ho
  have hi := hs.inw n hn
  have hrsi := hs.rsi
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, Nat.reducePow, addWord, runBlock_cons,
    runStep_some, runBlock_nil, exec, execAlu32, readSrc32, isa, VG.Proof.ChaCha20.X86_64.ea_at,
    State.load32, State.store32, State.setReg32, State.setReg, arithFlags, State.setFlags, hrsi, o,
    io, ii, ho, hi, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun j hj => ?_, fun j hj => ?_, hs.frame.writeW (List.mem_singleton_self _) _ cout,
    by simpa using hs.rsi, by simpa using hs.rsp, hs.rd, hs.wr⟩
  · by_cases hjn : j = n
    · subst hjn; simp [VG.Proof.ChaCha20.X86_64.bufAt, Mem.readW_writeW_self32]
    · rw [VG.Proof.ChaCha20.X86_64.readW_writeW_off _ _ _ (by lit_omega) (by simp [outOff]; omega) (by simp [outOff]; omega)
        (by simp [outOff]; omega), hs.out j hj]
      split <;> split <;> first | rfl | omega
  · rw [VG.Proof.ChaCha20.X86_64.readW_writeW_off _ _ _ (by lit_omega) (by simp [inOff]; omega) (by simp [outOff]; omega)
      (by simp [inOff, outOff]; omega)]
    exact hs.inw j hj

/-! ## Phase 1: saving the callee-saved registers -/

theorem saved_bound : ∀ p ∈ VG.Impl.ChaCha20.X86_64.saved, 144 ≤ p.2 ∧ p.2 + 8 ≤ 192 := by decide

theorem slot_buf {ws : List Region} {buf : Addr} (hw : VG.Proof.ChaCha20.X86_64.bufR buf ∈ ws) {p : Reg × Nat}
    (hp : p ∈ VG.Impl.ChaCha20.X86_64.saved) : InRegions ws (Spill.slot buf p.2) 8 := by
  have := VG.Proof.ChaCha20.X86_64.saved_bound p hp
  exact ⟨VG.Proof.ChaCha20.X86_64.bufR buf, hw, Offset.contains_base _ (by omega) (by omega)⟩

/-- The memory after the prologue's stores. -/
abbrev saveMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (VG.Proof.ChaCha20.X86_64.buf s₀) s₀.gpr VG.Impl.ChaCha20.X86_64.saved

/-- The callee-saved registers are saved in `buf`. -/
abbrev Saved (s₀ : State) (m : Mem) : Prop := Spill.Saved m (VG.Proof.ChaCha20.X86_64.buf s₀) s₀.gpr VG.Impl.ChaCha20.X86_64.saved

theorem save_ok {s₀ : State} (hp : VG.Proof.ChaCha20.X86_64.Pre s₀) :
    WP isa (.block VG.Impl.ChaCha20.X86_64.save) s₀ fun s₁ =>
      s₁.gpr = s₀.gpr ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.mem = VG.Proof.ChaCha20.X86_64.saveMem s₀ :=
  Spill.save_ok .rsi VG.Impl.ChaCha20.X86_64.saved s₀ fun _ hp' => VG.Proof.ChaCha20.X86_64.slot_buf hp.hw hp'

theorem saveMem_saved (s₀ : State) : VG.Proof.ChaCha20.X86_64.Saved s₀ (VG.Proof.ChaCha20.X86_64.saveMem s₀) :=
  Spill.saveMem_saved _ _ _ _ (by decide)

theorem saveMem_frame (s₀ : State) : Frame [VG.Proof.ChaCha20.X86_64.bufR (VG.Proof.ChaCha20.X86_64.buf s₀)] s₀.mem (VG.Proof.ChaCha20.X86_64.saveMem s₀) :=
  Spill.saveMem_frame_base _ _ _ _ (fun p hp => by have := VG.Proof.ChaCha20.X86_64.saved_bound p hp; omega) (by decide)

theorem saved_frame {s₀ : State} {m m' : Mem} (h : VG.Proof.ChaCha20.X86_64.Saved s₀ m) (hf : Frame [VG.Proof.ChaCha20.X86_64.workR (VG.Proof.ChaCha20.X86_64.buf s₀)] m m') :
    VG.Proof.ChaCha20.X86_64.Saved s₀ m' := by
  refine Spill.Saved.frame h hf fun p hp r hr => ?_
  rw [List.mem_singleton.mp hr]
  have := VG.Proof.ChaCha20.X86_64.saved_bound p hp
  have hd := VG.Proof.ChaCha20.X86_64.disjoint_sub (VG.Proof.ChaCha20.X86_64.buf s₀) (a := p.2) (la := 8) (b := 0) (lb := 144) (by omega) (by omega)
    (by lit_omega)
  simp only [VG.Proof.ChaCha20.X86_64.bufAt, VG.Proof.ChaCha20.X86_64.ofInt_natCast] at hd
  exact hd

/-! ## Phase 3: loading the registers -/

theorem load_eq : load = [
    .mov32 .rax (.mem (at_ .rsi (inOff 0))), .mov32 .rbx (.mem (at_ .rsi (inOff 1))),
    .mov32 .rcx (.mem (at_ .rsi (inOff 2))), .mov32 .rdx (.mem (at_ .rsi (inOff 3))),
    .mov32 .rdi (.mem (at_ .rsi (inOff 4))), .mov32 .rbp (.mem (at_ .rsi (inOff 5))),
    .mov32 .r8 (.mem (at_ .rsi (inOff 6))), .mov32 .r9 (.mem (at_ .rsi (inOff 7))),
    .mov32 .r14 (.mem (at_ .rsi (inOff 8))), .mov32 .r15 (.mem (at_ .rsi (inOff 9))),
    .mov32 .r10 (.mem (at_ .rsi (inOff 12))), .mov32 .r11 (.mem (at_ .rsi (inOff 13))),
    .mov32 .r12 (.mem (at_ .rsi (inOff 14))), .mov32 .r13 (.mem (at_ .rsi (inOff 15)))] := rfl

set_option simprocs false in
theorem load_ok {s₀ s₁ : State} (hp : VG.Proof.ChaCha20.X86_64.Pre s₀) (h₁ : s₁.gpr = s₀.gpr) {s : State}
    (hc : VG.Proof.ChaCha20.X86_64.CI s₀ s₁ 16 s) :
    WP isa (.block load) s fun s' =>
      VG.Proof.ChaCha20.X86_64.Holds (VG.Proof.ChaCha20.X86_64.buf s₀) false (VG.Proof.ChaCha20.X86_64.V s₀) s' ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.gpr .rsi = VG.Proof.ChaCha20.X86_64.buf s₀ ∧ s'.gpr .rsp = s₀.gpr .rsp := by
  have hrsi : s.gpr .rsi = VG.Proof.ChaCha20.X86_64.buf s₀ := by rw [hc.gpr _ (by decide), h₁]
  have hrsp : s.gpr .rsp = s₀.gpr .rsp := by rw [hc.gpr _ (by decide), h₁]
  have hw : VG.Proof.ChaCha20.X86_64.bufR (VG.Proof.ChaCha20.X86_64.buf s₀) ∈ s.wr := by rw [hc.wr]; exact hp.hw
  have hin : ∀ k, k < 16 → InRegions (s.rd ++ s.wr) (VG.Proof.ChaCha20.X86_64.buf s₀ + BitVec.ofInt 64 ((inOff k : Nat) : Int)) 4 :=
    fun k hk => VG.Proof.ChaCha20.X86_64.in_buf hw (VG.Proof.ChaCha20.X86_64.in_lt hk)
  have v : ∀ k (hk : k < 16), s.mem.readW (VG.Proof.ChaCha20.X86_64.buf s₀ + BitVec.ofInt 64 ((inOff k : Nat) : Int)) 32 =
      (VG.Proof.ChaCha20.X86_64.V s₀)[k] := fun k hk => hc.inw k hk hk
  apply WP.of_runBlock
  rw [VG.Proof.ChaCha20.X86_64.load_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc32, isa, VG.Proof.ChaCha20.X86_64.ea_at, State.load32,
    State.setReg32, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, hrsi,
    hin _ (show 0 < 16 by decide), hin _ (show 1 < 16 by decide),
    hin _ (show 2 < 16 by decide), hin _ (show 3 < 16 by decide), hin _ (show 4 < 16 by decide),
    hin _ (show 5 < 16 by decide), hin _ (show 6 < 16 by decide), hin _ (show 7 < 16 by decide),
    hin _ (show 8 < 16 by decide), hin _ (show 9 < 16 by decide), hin _ (show 12 < 16 by decide),
    hin _ (show 13 < 16 by decide), hin _ (show 14 < 16 by decide), hin _ (show 15 < 16 by decide),
    ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun k hk => ?_, trivial, trivial, trivial, by simp (config := {decide := true}),
    by simp (config := {decide := true}) [hrsp]⟩
  have v' : ∀ k (hk : k < 16), s.mem.readW (VG.Proof.ChaCha20.X86_64.buf s₀ + BitVec.ofNat 64 (inOff k)) 32 = (VG.Proof.ChaCha20.X86_64.V s₀)[k] :=
    fun k hk => by rw [← VG.Proof.ChaCha20.X86_64.ofInt_natCast]; exact v k hk
  have sl : ∀ k (hk : k < 16), (k = 10 ∨ k = 11) →
      s.mem.readW (VG.Proof.ChaCha20.X86_64.buf s₀ + BitVec.ofNat 64 (VG.Impl.ChaCha20.X86_64.slotOff k)) 32 = (VG.Proof.ChaCha20.X86_64.V s₀)[k] :=
    fun k hk h => by rw [← VG.Proof.ChaCha20.X86_64.ofInt_natCast]; exact hc.slot k hk hk h
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;>
  first
    | omega
    | simp (config := {decide := true}) only [wreg, VG.Proof.ChaCha20.X86_64.slotAddr, ite_true, ite_false, VG.Proof.ChaCha20.X86_64.ofInt_natCast,
        RegUpd.gpr_setReg, RegUpd.mem_setReg] <;>
      first
        | rw [v' _ (by decide)]
        | exact sl _ (by decide) (by decide)

/-! ## Phase 7: restoring the callee-saved registers -/

theorem restore_ok {s₀ : State} {s : State} (hs : VG.Proof.ChaCha20.X86_64.Saved s₀ s.mem) (hrsi : s.gpr .rsi = VG.Proof.ChaCha20.X86_64.buf s₀)
    (hw : VG.Proof.ChaCha20.X86_64.bufR (VG.Proof.ChaCha20.X86_64.buf s₀) ∈ s.wr) :
    WP isa (.block VG.Impl.ChaCha20.X86_64.restore) s fun s' =>
      s'.mem = s.mem ∧ s'.gpr .rsp = s.gpr .rsp ∧
      ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15], s'.gpr r = s₀.gpr r := by
  have hsub : ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15], r ∈ saved.map Prod.fst := by decide
  refine WP.mono (Spill.restore_ok .rsi VG.Impl.ChaCha20.X86_64.saved s₀.gpr s (by decide)
    (fun p hp => by rw [hrsi]; exact VG.Proof.ChaCha20.X86_64.slot_buf (List.mem_append_right _ hw) hp) (by rw [hrsi]; exact hs))
    fun s' ⟨h₁, h₂, hm, _⟩ => ⟨hm, h₂ _ (by decide), fun r hr => h₁ r (hsub r hr)⟩

/-! ## The whole function -/

/-- The result of the rounds. -/
abbrev Rs (s₀ : State) : CState := Nat.repeat innerBlock 10 (VG.Proof.ChaCha20.X86_64.V s₀)

theorem finish_split : VG.Impl.ChaCha20.X86_64.finish ++ VG.Impl.ChaCha20.X86_64.restore =
    ((List.range 16).flatMap storeWord ++ (List.range 16).flatMap addWord) ++ VG.Impl.ChaCha20.X86_64.restore := by
  unfold VG.Impl.ChaCha20.X86_64.finish; rfl

theorem read_in {p : Addr} {m m' : Mem} {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, ∀ j < 16, (⟨VG.Proof.ChaCha20.X86_64.bufAt p (inOff j), 4⟩ : Region).Disjoint r)
    {j : Nat} (hj : j < 16) :
    m'.readW (VG.Proof.ChaCha20.X86_64.bufAt p (inOff j)) 32 = m.readW (VG.Proof.ChaCha20.X86_64.bufAt p (inOff j)) 32 :=
  hf.readW (Region.contains_self _ _) (fun r hr => hd r hr j hj) (by decide)

theorem block_post {p : Addr} {m : Mem} {R v : CState}
    (h : ∀ j (hj : j < 16), m.readW (VG.Proof.ChaCha20.X86_64.bufAt p (outOff j)) 32 = R[j] + v[j]) :
    stateAt m p = Vector.zipWith (· + ·) R v := by
  apply Vector.ext
  intro j hj
  simp only [stateAt, Vector.getElem_ofFn, Vector.getElem_zipWith]
  have := h j hj
  simp only [VG.Proof.ChaCha20.X86_64.bufAt, outOff, VG.Proof.ChaCha20.X86_64.ofInt_natCast] at this
  exact this

theorem correct {s₀ : State} (hp : VG.Proof.ChaCha20.X86_64.Pre s₀) :
    WP isa block s₀ fun s' => gprPreserved s₀ s' ∧ Proof.ChaCha20.blockX86_64.post s₀ s' := by
  have hw₀ := hp.hw
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (VG.Proof.ChaCha20.X86_64.save_ok hp) fun s₁ ⟨hg₁, hrd₁, hwr₁, hm₁⟩ => ?_
  have hf₁ : Frame [VG.Proof.ChaCha20.X86_64.bufR (VG.Proof.ChaCha20.X86_64.buf s₀)] s₀.mem s₁.mem := hm₁ ▸ VG.Proof.ChaCha20.X86_64.saveMem_frame s₀
  have hc₀ : VG.Proof.ChaCha20.X86_64.CI s₀ s₁ 0 s₁ :=
    ⟨fun _ _ => rfl, hrd₁, hwr₁, Frame.refl _ _, fun _ _ h => absurd h (by lit_omega),
      fun _ _ h => absurd h (by lit_omega)⟩
  refine WP.mono (wp_range_flatMap (VG.Proof.ChaCha20.X86_64.CI s₀ s₁) (fun k s hk hc => VG.Proof.ChaCha20.X86_64.copy_step hp hg₁ hf₁ hk hc)
    16 (Nat.le_refl _) s₁ hc₀) fun s hc => ?_
  refine WP.mono (VG.Proof.ChaCha20.X86_64.load_ok hp hg₁ hc) fun s₂ ⟨hh₂, hm₂, hrd₂, hwr₂, hrsi₂, hrsp₂⟩ => ?_
  have hw₂ : VG.Proof.ChaCha20.X86_64.bufR (VG.Proof.ChaCha20.X86_64.buf s₀) ∈ s₂.wr := by rw [hwr₂, hc.wr]; exact hw₀
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86_64.rounds_ok hh₂ hrsi₂ hw₂ 10) fun s₃ hR => ?_)
  have hw₃ : VG.Proof.ChaCha20.X86_64.bufR (VG.Proof.ChaCha20.X86_64.buf s₀) ∈ s₃.wr := by rw [hR.wr]; exact hw₂
  rw [VG.Proof.ChaCha20.X86_64.finish_split, WP.block_append_iff, WP.block_append_iff]
  have hs₀ : VG.Proof.ChaCha20.X86_64.SI (VG.Proof.ChaCha20.X86_64.buf s₀) (VG.Proof.ChaCha20.X86_64.Rs s₀) s₃ 0 s₃ :=
    ⟨fun _ _ h => absurd h (by lit_omega), fun j hj _ => hR.holds j hj, Frame.refl _ _,
      hR.rsi.trans hrsi₂, rfl, rfl, rfl⟩
  refine WP.mono (wp_range_flatMap (VG.Proof.ChaCha20.X86_64.SI (VG.Proof.ChaCha20.X86_64.buf s₀) (VG.Proof.ChaCha20.X86_64.Rs s₀) s₃)
    (fun k s hk hs => VG.Proof.ChaCha20.X86_64.store_step hw₃ hk hs) 16 (Nat.le_refl _) s₃ hs₀) fun s₄ hS => ?_
  have hw₄ : VG.Proof.ChaCha20.X86_64.bufR (VG.Proof.ChaCha20.X86_64.buf s₀) ∈ s₄.wr := by rw [hS.wr]; exact hw₃
  have hinw : ∀ j (hj : j < 16), s₄.mem.readW (VG.Proof.ChaCha20.X86_64.bufAt (VG.Proof.ChaCha20.X86_64.buf s₀) (inOff j)) 32 = (VG.Proof.ChaCha20.X86_64.V s₀)[j] := by
    intro j hj
    rw [VG.Proof.ChaCha20.X86_64.read_in hS.frame (by
        intro r hr j hj
        simp only [List.mem_singleton] at hr; subst hr
        exact VG.Proof.ChaCha20.X86_64.disjoint_sub _ (by simp only [inOff]; omega) (by simp only [inOff]; omega) (by lit_omega)) hj,
      VG.Proof.ChaCha20.X86_64.read_in hR.frame (by
        intro r hr j hj
        simp only [List.mem_singleton] at hr; subst hr
        exact VG.Proof.ChaCha20.X86_64.disjoint_sub _ (by simp only [inOff]; omega) (by simp only [inOff]; omega) (by lit_omega)) hj,
      hm₂]
    exact hc.inw j hj hj
  have ha₀ : VG.Proof.ChaCha20.X86_64.AI (VG.Proof.ChaCha20.X86_64.buf s₀) (VG.Proof.ChaCha20.X86_64.Rs s₀) (VG.Proof.ChaCha20.X86_64.V s₀) s₄ 0 s₄ :=
    ⟨fun j hj => by simp only [Nat.not_lt_zero, ite_false]; exact hS.out j hj hj, hinw,
      Frame.refl _ _, hS.rsi, rfl, rfl, rfl⟩
  refine WP.mono (wp_range_flatMap (VG.Proof.ChaCha20.X86_64.AI (VG.Proof.ChaCha20.X86_64.buf s₀) (VG.Proof.ChaCha20.X86_64.Rs s₀) (VG.Proof.ChaCha20.X86_64.V s₀) s₄)
    (fun k s hk ha => VG.Proof.ChaCha20.X86_64.add_step hw₄ hk ha) 16 (Nat.le_refl _) s₄ ha₀) fun s₅ hA => ?_
  have hw₅ : VG.Proof.ChaCha20.X86_64.bufR (VG.Proof.ChaCha20.X86_64.buf s₀) ∈ s₅.wr := by rw [hA.wr]; exact hw₄
  -- Everything since the prologue's stores wrote only `[buf, buf + 144)`.
  have hwork : Frame [VG.Proof.ChaCha20.X86_64.workR (VG.Proof.ChaCha20.X86_64.buf s₀)] s₁.mem s₅.mem := by
    refine (VG.Proof.ChaCha20.X86_64.frame_work (a := 64) (len := 80) (by lit_omega) hc.frame).trans ?_
    rw [← hm₂]
    refine (VG.Proof.ChaCha20.X86_64.frame_work (a := 128) (len := 16) (by lit_omega) hR.frame).trans ?_
    exact (VG.Proof.ChaCha20.X86_64.frame_work (a := 0) (len := 64) (by lit_omega) hS.frame).trans
      (VG.Proof.ChaCha20.X86_64.frame_work (a := 0) (len := 64) (by lit_omega) hA.frame)
  have hsaved : VG.Proof.ChaCha20.X86_64.Saved s₀ s₅.mem := VG.Proof.ChaCha20.X86_64.saved_frame (hm₁ ▸ VG.Proof.ChaCha20.X86_64.saveMem_saved s₀) hwork
  have hbuf : Frame [VG.Proof.ChaCha20.X86_64.bufR (VG.Proof.ChaCha20.X86_64.buf s₀)] s₀.mem s₅.mem :=
    hf₁.trans (hwork.sub fun r hr => ⟨VG.Proof.ChaCha20.X86_64.bufR (VG.Proof.ChaCha20.X86_64.buf s₀), List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.ChaCha20.X86_64.sub_buf _ (by lit_omega)⟩)
  refine WP.mono (VG.Proof.ChaCha20.X86_64.restore_ok hsaved hA.rsi hw₅) fun s' ⟨hm', hrsp', hg'⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg' _ (by simp)
    · exact hg' _ (by simp)
    · rw [hrsp', hA.rsp, hS.rsp, hR.rsp, hrsp₂]
    · exact hg' _ (by simp)
    · exact hg' _ (by simp)
    · exact hg' _ (by simp)
    · exact hg' _ (by simp)
  · rw [hm']
    exact hbuf.readW (r := VG.Proof.ChaCha20.X86_64.retR s₀) (Region.contains_self _ _) (by simpa using hp.ret_buf)
      (by decide)
  · show stateAt s'.mem (VG.Proof.ChaCha20.X86_64.buf s₀) = Spec.ChaCha20.block (VG.Proof.ChaCha20.X86_64.V s₀)
    rw [hm']
    exact VG.Proof.ChaCha20.X86_64.block_post fun j hj => by simpa [hj] using hA.out j hj

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 64⟩]
  wr := [⟨0x2000, 256⟩]

theorem block_correct (s : State) (hs : Proof.ChaCha20.blockX86_64.pre s) :
    ∃ t s', Exec isa block s t s' ∧ abiPreserved s s' ∧ Proof.ChaCha20.blockX86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := VG.Proof.ChaCha20.X86_64.correct (VG.Proof.ChaCha20.X86_64.pre_of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

theorem block_ct : ConstantTime isa Proof.ChaCha20.blockX86_64.pre Proof.ChaCha20.blockX86_64.pub block := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> with_reducible assumption

theorem block_verified :
    Verified X86_64.target Impl.ChaCha20.X86_64.block (Spec.ChaCha20.blockContract X86_64.abi) :=
  Verified.of_correct VG.Proof.ChaCha20.X86_64.block_correct VG.Proof.ChaCha20.X86_64.block_ct (by
    sig_implies [Spec.ChaCha20.blockContract, Spec.ChaCha20.blockSig, X86_64.abi, X86_64.argRegs,
      Proof.ChaCha20.blockX86_64]
      [satState] using VG.Proof.ChaCha20.X86_64.satState)

end VG.Proof.ChaCha20.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.X86_64.Xor`. -/
section

/-!
# ChaCha20 keystream XOR on x86-64
-/

namespace VG.Proof.ChaCha20

open Spec.ChaCha20 VG.X86_64

/-- X86-64 contract for `vg_chacha20_xor(state: *mut [u32; 16], data: *mut u8,
len: usize, buf: *mut [u32; 80])`: XORs the first `len` bytes of the keystream
of the state at `state` into the `len` bytes at `data`.

The code may read and write `state` (64 bytes; its contents on exit are
unspecified), `data` (`len` bytes) and `buf` (320 bytes of working space).
They may not overlap each other, the return address on the stack, or the 8
bytes below it, where the call of the block function stores its return
address; `data` does not wrap around the end of the address space. The
pointers and the length are public; the state and the data are secret. -/
def xorX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 64⟩
    let data : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
    let buf : Region := ⟨s.gpr .rcx, 320⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [] ∧ s.wr = [state, data, buf] ∧
    state.Disjoint data ∧ state.Disjoint buf ∧ data.Disjoint buf ∧
    ret.Disjoint state ∧ ret.Disjoint data ∧ ret.Disjoint buf ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint buf ∧
    (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64
  post s s' :=
    bytesAt s'.mem (s.gpr .rsi) (s.gpr .rdx).toNat =
      List.zipWith (· ^^^ ·) (bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)
        (keystream (stateAt s.mem (s.gpr .rdi)) (s.gpr .rdx).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `xorX86_64` with `k` bytes of stack below the return address, for an
implementation whose calls use them, and that returns with `rsi` pointing at
`buf` (for a caller that recomputes pointers from it): what callers of any
implementation of `vg_chacha20_xor` rely on (see `Variant.lean`). -/
def xorStack (k : Nat) : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 64⟩
    let data : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
    let buf : Region := ⟨s.gpr .rcx, 320⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 k, k⟩
    s.rd = [] ∧ s.wr = [state, data, buf] ∧
    state.Disjoint data ∧ state.Disjoint buf ∧ data.Disjoint buf ∧
    ret.Disjoint state ∧ ret.Disjoint data ∧ ret.Disjoint buf ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint buf ∧
    (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64
  post s s' := xorX86_64.post s s' ∧ s'.gpr .rsi = s.gpr .rcx
  pub := xorX86_64.pub

theorem xorStack_pre8 : (VG.Proof.ChaCha20.xorStack 8).pre = xorX86_64.pre := rfl

end VG.Proof.ChaCha20

namespace VG.Proof.ChaCha20.X86_64.Xor

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Xor
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Proof.ChaCha20.X86_64 (toNat_ofNat_lt contains_off ea_at ofInt_natCast readW_writeW_off
  block_correct)
open VG.Spec.ChaCha20 (stateAt keystream serialize bytesAt)

/-- `p + d`, as the code computes it. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofInt 64 (d : Int)

/-! ## The entry state -/

section
variable (s₀ : State)
abbrev st : Addr := s₀.gpr .rdi
abbrev dp : Addr := s₀.gpr .rsi
abbrev L : Nat := (s₀.gpr .rdx).toNat
abbrev bp : Addr := s₀.gpr .rcx
abbrev stR : Region := ⟨VG.Proof.ChaCha20.X86_64.Xor.st s₀, 64⟩
abbrev dR : Region := ⟨VG.Proof.ChaCha20.X86_64.Xor.dp s₀, VG.Proof.ChaCha20.X86_64.Xor.L s₀⟩
abbrev bR : Region := ⟨VG.Proof.ChaCha20.X86_64.Xor.bp s₀, 320⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev stackR : Region := below (s₀.gpr .rsp) 8
/-- The state, the data and the keystream on entry. -/
abbrev S0 : CState := stateAt s₀.mem (VG.Proof.ChaCha20.X86_64.Xor.st s₀)
abbrev D0 (k : Nat) : Byte := s₀.mem (VG.Proof.ChaCha20.X86_64.Xor.dp s₀ + BitVec.ofNat 64 k)
abbrev KS : List Byte := keystream (VG.Proof.ChaCha20.X86_64.Xor.S0 s₀) (VG.Proof.ChaCha20.X86_64.Xor.L s₀)
/-- The bytes of data done before block `j`. -/
abbrev P (j : Nat) : Nat := min (64 * j) (VG.Proof.ChaCha20.X86_64.Xor.L s₀)
end

theorem L_lt (s₀ : State) : VG.Proof.ChaCha20.X86_64.Xor.L s₀ < 2 ^ 64 := (s₀.gpr .rdx).isLt

structure XPre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [VG.Proof.ChaCha20.X86_64.Xor.stR s₀, VG.Proof.ChaCha20.X86_64.Xor.dR s₀, VG.Proof.ChaCha20.X86_64.Xor.bR s₀]
  st_d : (VG.Proof.ChaCha20.X86_64.Xor.stR s₀).Disjoint (VG.Proof.ChaCha20.X86_64.Xor.dR s₀)
  st_b : (VG.Proof.ChaCha20.X86_64.Xor.stR s₀).Disjoint (VG.Proof.ChaCha20.X86_64.Xor.bR s₀)
  d_b : (VG.Proof.ChaCha20.X86_64.Xor.dR s₀).Disjoint (VG.Proof.ChaCha20.X86_64.Xor.bR s₀)
  ret_st : (VG.Proof.ChaCha20.X86_64.Xor.retR s₀).Disjoint (VG.Proof.ChaCha20.X86_64.Xor.stR s₀)
  ret_d : (VG.Proof.ChaCha20.X86_64.Xor.retR s₀).Disjoint (VG.Proof.ChaCha20.X86_64.Xor.dR s₀)
  ret_b : (VG.Proof.ChaCha20.X86_64.Xor.retR s₀).Disjoint (VG.Proof.ChaCha20.X86_64.Xor.bR s₀)
  stk_st : (VG.Proof.ChaCha20.X86_64.Xor.stackR s₀).Disjoint (VG.Proof.ChaCha20.X86_64.Xor.stR s₀)
  stk_d : (VG.Proof.ChaCha20.X86_64.Xor.stackR s₀).Disjoint (VG.Proof.ChaCha20.X86_64.Xor.dR s₀)
  stk_b : (VG.Proof.ChaCha20.X86_64.Xor.stackR s₀).Disjoint (VG.Proof.ChaCha20.X86_64.Xor.bR s₀)
  nowrap : (VG.Proof.ChaCha20.X86_64.Xor.dp s₀).toNat + VG.Proof.ChaCha20.X86_64.Xor.L s₀ ≤ 2 ^ 64

theorem XPre.of (s₀ : State) (h : Proof.ChaCha20.xorX86_64.pre s₀) : VG.Proof.ChaCha20.X86_64.Xor.XPre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-- Our caller's `rbx, rbp, r12`, saved in `buf[256, 280)`. -/
abbrev Saved (s₀ : State) (m : Mem) : Prop := Spill.Saved m (VG.Proof.ChaCha20.X86_64.Xor.bp s₀) s₀.gpr saved

theorem saved_bound : ∀ p ∈ saved, 256 ≤ p.2 ∧ p.2 + 8 ≤ 280 := by decide

/-- The regions the code writes: its buffers and the return address of its calls. -/
abbrev frameR (s₀ : State) : List Region := [VG.Proof.ChaCha20.X86_64.Xor.stR s₀, VG.Proof.ChaCha20.X86_64.Xor.dR s₀, VG.Proof.ChaCha20.X86_64.Xor.bR s₀, VG.Proof.ChaCha20.X86_64.Xor.stackR s₀]

/-- Before block `j` (the loop's invariant). -/
structure OInv (s₀ : State) (j : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = VG.Proof.ChaCha20.X86_64.Xor.st s₀
  rbp : s.gpr .rbp = VG.Proof.ChaCha20.X86_64.Xor.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Xor.P s₀ j)
  r12 : s.gpr .r12 = BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Xor.L s₀ - VG.Proof.ChaCha20.X86_64.Xor.P s₀ j)
  rsi : s.gpr .rsi = VG.Proof.ChaCha20.X86_64.Xor.bp s₀
  keep : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  cnt : stateAt s.mem (VG.Proof.ChaCha20.X86_64.Xor.st s₀) = ctr (VG.Proof.ChaCha20.X86_64.Xor.S0 s₀) j
  data : ∀ k < VG.Proof.ChaCha20.X86_64.Xor.L s₀, s.mem (VG.Proof.ChaCha20.X86_64.Xor.dp s₀ + BitVec.ofNat 64 k) =
    if k < VG.Proof.ChaCha20.X86_64.Xor.P s₀ j then VG.Proof.ChaCha20.X86_64.Xor.D0 s₀ k ^^^ (VG.Proof.ChaCha20.X86_64.Xor.KS s₀).getD k 0 else VG.Proof.ChaCha20.X86_64.Xor.D0 s₀ k
  saved : VG.Proof.ChaCha20.X86_64.Xor.Saved s₀ s.mem
  frame : Frame (VG.Proof.ChaCha20.X86_64.Xor.frameR s₀) s₀.mem s.mem

/-! ## Memory -/

theorem XPre.w_st {s₀ : State} (hp : VG.Proof.ChaCha20.X86_64.Xor.XPre s₀) : VG.Proof.ChaCha20.X86_64.Xor.stR s₀ ∈ s₀.wr := by simp [hp.wr]
theorem XPre.w_d {s₀ : State} (hp : VG.Proof.ChaCha20.X86_64.Xor.XPre s₀) : VG.Proof.ChaCha20.X86_64.Xor.dR s₀ ∈ s₀.wr := by simp [hp.wr]
theorem XPre.w_b {s₀ : State} (hp : VG.Proof.ChaCha20.X86_64.Xor.XPre s₀) : VG.Proof.ChaCha20.X86_64.Xor.bR s₀ ∈ s₀.wr := by simp [hp.wr]

/-- The state after its counter (word 12) is stored. -/
theorem stateAt_writeW_counter (m : Mem) (p : Addr) (v : BitVec 32) :
    stateAt (m.writeW (VG.Proof.ChaCha20.X86_64.Xor.off p 48) v) p = (stateAt m p).set 12 v := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn, Vector.getElem_set]
  have e : p + BitVec.ofNat 64 (4 * i) = VG.Proof.ChaCha20.X86_64.Xor.off p (4 * i) := by rw [VG.Proof.ChaCha20.X86_64.Xor.off, VG.Proof.ChaCha20.X86_64.ofInt_natCast]
  rw [e]
  by_cases h : 12 = i
  · subst h
    simp only [ite_true]
    exact Mem.readW_writeW_self32 _ _ _
  · simp only [h, ite_false]
    exact VG.Proof.ChaCha20.X86_64.readW_writeW_off m p v (Or.inl rfl) (by lit_omega) (by lit_omega) (by lit_omega)

theorem contains_ofNat {b : Addr} {len d n : Nat} (h : d + n ≤ len) (hd : d < 2 ^ 64) :
    (⟨b, len⟩ : Region).Contains (b + BitVec.ofNat 64 d) n := by
  have := VG.Proof.ChaCha20.X86_64.contains_off (base := b) h hd
  rwa [VG.Proof.ChaCha20.X86_64.ofInt_natCast] at this

/-- A state in memory outside a frame is unchanged. -/
theorem stateAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 64⟩ : Region).Disjoint r) : stateAt m' p = stateAt m p := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn]
  exact hf.readW (VG.Proof.ChaCha20.X86_64.Xor.contains_ofNat (by lit_omega) (by lit_omega)) hd (by decide)

/-! ## The prologue -/

theorem save_eq : save ++ ([.mov .rbx (.reg .rdi), .mov .rbp (.reg .rsi), .mov .r12 (.reg .rdx),
    .mov .rsi (.reg .rcx), .alu .test .r12 (.reg .r12)] : List Instr) =
    [.store (at_ .rcx 256) .rbx, .store (at_ .rcx 264) .rbp, .store (at_ .rcx 272) .r12,
    .mov .rbx (.reg .rdi), .mov .rbp (.reg .rsi), .mov .r12 (.reg .rdx),
    .mov .rsi (.reg .rcx), .alu .test .r12 (.reg .r12)] := rfl

theorem prologue_ok {s₀ : State} (hp : VG.Proof.ChaCha20.X86_64.Xor.XPre s₀) :
    WP isa (.block (save ++ ([.mov .rbx (.reg .rdi), .mov .rbp (.reg .rsi), .mov .r12 (.reg .rdx),
      .mov .rsi (.reg .rcx), .alu .test .r12 (.reg .r12)] : List Instr))) s₀ fun s =>
      VG.Proof.ChaCha20.X86_64.Xor.OInv s₀ 0 s ∧ s.zf = some (decide (VG.Proof.ChaCha20.X86_64.Xor.L s₀ = 0)) := by
  refine Spill.save_then .rcx saved (fun p hp' => ?_) ?_
  · have := VG.Proof.ChaCha20.X86_64.Xor.saved_bound p hp'
    exact ⟨_, hp.w_b, Offset.contains_base _ (by omega) (by lit_omega)⟩
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, execAlu, arithFlags, State.setReg, State.setFlags,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  have hf : Frame [VG.Proof.ChaCha20.X86_64.Xor.bR s₀] s₀.mem (Spill.saveMem s₀.mem (VG.Proof.ChaCha20.X86_64.Xor.bp s₀) s₀.gpr saved) :=
    Spill.saveMem_frame_base _ _ _ _ (fun p hp => by have := VG.Proof.ChaCha20.X86_64.Xor.saved_bound p hp; omega) (by decide)
  refine ⟨⟨by simp, by simp [VG.Proof.ChaCha20.X86_64.Xor.P],
    by simp [VG.Proof.ChaCha20.X86_64.Xor.P], by simp, fun r hr => ?_, rfl,
    rfl, ?_, fun k hk => ?_, ?_, hf.mono (by simp)⟩, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp
  · rw [VG.Proof.ChaCha20.X86_64.Xor.stateAt_frame hf (by simpa using hp.st_b), ctr_zero]
  · simp only [VG.Proof.ChaCha20.X86_64.Xor.P, Nat.mul_zero, Nat.zero_min, Nat.not_lt_zero, ite_false]
    exact hf.bytes (R := VG.Proof.ChaCha20.X86_64.Xor.dR s₀) (by simpa using hp.d_b) (Nat.le_of_lt (s₀.gpr .rdx).isLt) hk
  · exact Spill.saveMem_saved _ _ _ _ (by decide)
  · simp only [BitVec.and_self, VG.Proof.ChaCha20.X86_64.Xor.L]
    by_cases h : (s₀.gpr .rdx).toNat = 0
    · simp [BitVec.eq_of_toNat_eq (x := s₀.gpr .rdx) (y := 0) h]
    · have : s₀.gpr .rdx ≠ 0 := fun h' => h (by simp [h'])
      simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
      exact this

/-- The first 256 bytes of `buf`, which the block function may write. -/
abbrev b256 (s₀ : State) : Region := ⟨VG.Proof.ChaCha20.X86_64.Xor.bp s₀, 256⟩

/-- Where our caller's registers are saved. -/
abbrev savR (s₀ : State) : Region := ⟨VG.Proof.ChaCha20.X86_64.Xor.off (VG.Proof.ChaCha20.X86_64.Xor.bp s₀) 256, 24⟩

theorem savR_sub (s₀ : State) : Region.Sub (VG.Proof.ChaCha20.X86_64.Xor.savR s₀) (VG.Proof.ChaCha20.X86_64.Xor.bR s₀) := by
  simp only [VG.Proof.ChaCha20.X86_64.Xor.savR, VG.Proof.ChaCha20.X86_64.Xor.off, VG.Proof.ChaCha20.X86_64.ofInt_natCast]
  exact Offset.sub_base _ (by lit_omega)

theorem savR_b256 (s₀ : State) : (VG.Proof.ChaCha20.X86_64.Xor.savR s₀).Disjoint (VG.Proof.ChaCha20.X86_64.Xor.b256 s₀) := by
  simp only [VG.Proof.ChaCha20.X86_64.Xor.savR, VG.Proof.ChaCha20.X86_64.Xor.off, VG.Proof.ChaCha20.X86_64.ofInt_natCast]
  exact Offset.disjoint_base _ (by lit_omega) (by lit_omega)

/-- The saved registers survive a frame that does not touch them. -/
theorem Saved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : VG.Proof.ChaCha20.X86_64.Xor.Saved s₀ m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (VG.Proof.ChaCha20.X86_64.Xor.savR s₀).Disjoint r) : VG.Proof.ChaCha20.X86_64.Xor.Saved s₀ m' :=
  Spill.Saved.frame h hf fun p hp r hr => by
    have := VG.Proof.ChaCha20.X86_64.Xor.saved_bound p hp
    refine (hd r hr).sub_left ?_
    simp only [VG.Proof.ChaCha20.X86_64.Xor.savR, VG.Proof.ChaCha20.X86_64.Xor.off, VG.Proof.ChaCha20.X86_64.ofInt_natCast]
    exact Offset.sub _ (by omega) (by omega)

/-! ## Calling the block function -/

/-- The registers the block function never writes. -/
def kept : List Reg := [.rsi, .rsp]

theorem block_keeps : ((instrs Impl.ChaCha20.X86_64.block).all fun i =>
    kept.all fun r => !Taint.clobbers i r) = true := by
  rw [← Code.allInstrs_eq]; lit_decide

theorem block_keeps_reg {r : Reg} (hr : r ∈ VG.Proof.ChaCha20.X86_64.Xor.kept) :
    ∀ i ∈ instrs Impl.ChaCha20.X86_64.block, Taint.clobbers i r = false := by
  intro i hi
  have := List.all_eq_true.mp (List.all_eq_true.mp VG.Proof.ChaCha20.X86_64.Xor.block_keeps i hi) r hr
  simpa using this

theorem block_depth : Impl.ChaCha20.X86_64.block.depth = 0 := by lit_decide


theorem b256_sub (s₀ : State) : Region.Sub (VG.Proof.ChaCha20.X86_64.Xor.b256 s₀) (VG.Proof.ChaCha20.X86_64.Xor.bR s₀) := Region.sub_prefix (by lit_omega)

/-- After the block function: `buf` holds block `j`'s keystream. -/
structure AInv (s₀ : State) (j : Nat) (s : State) : Prop extends VG.Proof.ChaCha20.X86_64.Xor.OInv s₀ j s where
  ks : ∀ t < 64, s.mem (VG.Proof.ChaCha20.X86_64.Xor.bp s₀ + BitVec.ofNat 64 t) =
    (serialize (Spec.ChaCha20.block (ctr (VG.Proof.ChaCha20.X86_64.Xor.S0 s₀) j))).getD t 0

set_option simprocs false in
theorem call_ok {s₀ : State} (hp : VG.Proof.ChaCha20.X86_64.Xor.XPre s₀) {j : Nat} {s : State} (h : VG.Proof.ChaCha20.X86_64.Xor.OInv s₀ j s) :
    WP isa (.seq (.block [.mov .rdi (.reg .rbx)]) (.call "vg_chacha20_block" Impl.ChaCha20.X86_64.block))
      s (VG.Proof.ChaCha20.X86_64.Xor.AInv s₀ j) := by
  have h₁ : WP isa (.block [.mov .rdi (.reg .rbx)]) s fun s₁ =>
      s₁.gpr .rdi = VG.Proof.ChaCha20.X86_64.Xor.st s₀ ∧ (∀ r, r ≠ .rdi → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧
        s₁.mem = s.mem := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, isa, Option.map_some,
      Option.some.injEq, exists_eq_left']
    exact ⟨by simp [State.setReg, h.rbx], fun r hr => by simp [State.setReg, hr], rfl, rfl, rfl⟩
  refine WP.seq (WP.mono h₁ fun s₁ ⟨e₁, e₂, e₃, e₄, e₅⟩ => ?_)
  have hsp : s₁.gpr .rsp = s₀.gpr .rsp := by rw [e₂ _ (by decide)]; exact h.keep .rsp (by simp)
  have hrsi : s₁.gpr .rsi = VG.Proof.ChaCha20.X86_64.Xor.bp s₀ := by rw [e₂ _ (by decide)]; exact h.rsi
  have hne : ∀ r : Reg, r ≠ .rsp → s₁.callEntry.gpr r = s₁.gpr r := fun r h => State.callEntry_gpr _ h
  have hwr : s₁.wr = [VG.Proof.ChaCha20.X86_64.Xor.stR s₀, VG.Proof.ChaCha20.X86_64.Xor.dR s₀, VG.Proof.ChaCha20.X86_64.Xor.bR s₀] := by rw [e₄, h.wr, hp.wr]
  have hrd : s₁.rd = [] := by rw [e₃, h.rd, hp.rd]
  have hstk : below (s₁.gpr .rsp) 8 = VG.Proof.ChaCha20.X86_64.Xor.stackR s₀ := by rw [hsp]
  refine WP.call (k := Proof.ChaCha20.blockX86_64) VG.Proof.ChaCha20.X86_64.block_correct (VG.Proof.ChaCha20.X86_64.Xor.block_keeps_reg (by simp [VG.Proof.ChaCha20.X86_64.Xor.kept]))
    (by rw [VG.Proof.ChaCha20.X86_64.Xor.block_depth]; decide) (rd := [VG.Proof.ChaCha20.X86_64.Xor.stR s₀]) (wr := [VG.Proof.ChaCha20.X86_64.Xor.b256 s₀]) ?_ ?_ ?_ ?_
  · simp only [Proof.ChaCha20.blockX86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, hne _ (by decide : Reg.rdi ≠ .rsp),
      hne _ (by decide : Reg.rsi ≠ .rsp), e₁, hrsi, hsp]
    exact ⟨trivial, trivial, (hp.st_b.sub_right (VG.Proof.ChaCha20.X86_64.Xor.b256_sub s₀)).symm,
      hp.stk_b.sub_right (VG.Proof.ChaCha20.X86_64.Xor.b256_sub s₀)⟩
  · rw [hrd, hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.ChaCha20.X86_64.Xor.stR s₀, by simp, 0, by simp, show 0 + 64 ≤ 64 by omega⟩
    · exact ⟨VG.Proof.ChaCha20.X86_64.Xor.bR s₀, by simp, 0, by simp, show 0 + 256 ≤ 320 by omega⟩
  · rw [hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨VG.Proof.ChaCha20.X86_64.Xor.bR s₀, by simp, 0, by simp, show 0 + 256 ≤ 320 by omega⟩
  · intro s₂ hrd₂ hwr₂ hcs hf hkeep ⟨s₃, hm₃, _, hpost⟩
    rw [VG.Proof.ChaCha20.X86_64.Xor.block_depth, hstk] at hf
    have g : ∀ r ∈ calleeSaved, r ≠ .rdi → s₂.gpr r = s.gpr r := fun r hr hne => by
      rw [hcs r hr, e₂ r hne]
    have hd : ∀ R : Region, R.Disjoint (VG.Proof.ChaCha20.X86_64.Xor.b256 s₀) → R.Disjoint (VG.Proof.ChaCha20.X86_64.Xor.stackR s₀) →
        ∀ r ∈ [VG.Proof.ChaCha20.X86_64.Xor.b256 s₀] ++ [VG.Proof.ChaCha20.X86_64.Xor.stackR s₀], R.Disjoint r := by
      intro R h₁ h₂ r hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> with_reducible assumption
    have hst : stateAt s₂.mem (VG.Proof.ChaCha20.X86_64.Xor.st s₀) = stateAt s₁.mem (VG.Proof.ChaCha20.X86_64.Xor.st s₀) :=
      VG.Proof.ChaCha20.X86_64.Xor.stateAt_frame hf (hd _ (hp.st_b.sub_right (VG.Proof.ChaCha20.X86_64.Xor.b256_sub s₀)) hp.stk_st.symm)
    refine ⟨⟨by rw [g .rbx (by simp [calleeSaved]) (by decide), h.rbx],
      by rw [g .rbp (by simp [calleeSaved]) (by decide), h.rbp],
      by rw [g .r12 (by simp [calleeSaved]) (by decide), h.r12],
      by rw [hkeep .rsi (VG.Proof.ChaCha20.X86_64.Xor.block_keeps_reg (by simp [VG.Proof.ChaCha20.X86_64.Xor.kept])), hrsi],
      fun r hr => ?_, by rw [hrd₂, e₃, h.rd], by rw [hwr₂, e₄, h.wr],
      by rw [hst, e₅, h.cnt], fun k hk => ?_, ?_, ?_⟩, fun t ht => ?_⟩
    · have hr' : r ∈ calleeSaved ∧ r ≠ .rdi := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> simp (config := {decide := true})
      rw [g r hr'.1 hr'.2]
      exact h.keep r hr
    · rw [hf.bytes (R := VG.Proof.ChaCha20.X86_64.Xor.dR s₀) (hd _ (hp.d_b.sub_right (VG.Proof.ChaCha20.X86_64.Xor.b256_sub s₀)) hp.stk_d.symm)
        (Nat.le_of_lt (s₀.gpr .rdx).isLt) hk, e₅]
      exact h.data k hk
    · rw [e₅] at hf
      exact h.saved.frame hf (hd _ (VG.Proof.ChaCha20.X86_64.Xor.savR_b256 s₀) (hp.stk_b.symm.sub_left (VG.Proof.ChaCha20.X86_64.Xor.savR_sub s₀)))
    · rw [e₅] at hf
      exact h.frame.trans (hf.sub fun r hr => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨VG.Proof.ChaCha20.X86_64.Xor.bR s₀, by simp, VG.Proof.ChaCha20.X86_64.Xor.b256_sub s₀⟩
        · exact ⟨VG.Proof.ChaCha20.X86_64.Xor.stackR s₀, by simp, fun _ h => h⟩)
    · have hce : stateAt s₁.callEntry.mem (VG.Proof.ChaCha20.X86_64.Xor.st s₀) = stateAt s₁.mem (VG.Proof.ChaCha20.X86_64.Xor.st s₀) := by
        rw [State.callEntry_mem]
        exact VG.Proof.ChaCha20.X86_64.Xor.stateAt_frame (rs := [VG.Proof.ChaCha20.X86_64.Xor.stackR s₀])
          ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
            rw [← hstk]; exact below_call _ (by lit_omega) (by lit_omega)))
          (by simpa using hp.stk_st.symm)
      simp only [Proof.ChaCha20.blockX86_64, State.withRegions_gpr, State.withRegions_mem,
        hne _ (by decide : Reg.rdi ≠ .rsp), hne _ (by decide : Reg.rsi ≠ .rsp), e₁, hrsi, hm₃, hce,
        e₅, h.cnt] at hpost
      rw [← serialize_stateAt s₂.mem (VG.Proof.ChaCha20.X86_64.Xor.bp s₀) ht, hpost]

/-! ## The bytes of block `j` -/

/-- How many bytes of block `j` are used. -/
abbrev C (s₀ : State) (j : Nat) : Nat := min 64 (VG.Proof.ChaCha20.X86_64.Xor.L s₀ - VG.Proof.ChaCha20.X86_64.Xor.P s₀ j)

/-- Before byte `i` of block `j`. -/
structure IInv (s₀ : State) (j i : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = VG.Proof.ChaCha20.X86_64.Xor.st s₀
  rbp : s.gpr .rbp = VG.Proof.ChaCha20.X86_64.Xor.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Xor.P s₀ j)
  r12 : s.gpr .r12 = BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Xor.L s₀ - VG.Proof.ChaCha20.X86_64.Xor.P s₀ j)
  rsi : s.gpr .rsi = VG.Proof.ChaCha20.X86_64.Xor.bp s₀
  rdx : s.gpr .rdx = BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Xor.C s₀ j)
  rcx : s.gpr .rcx = BitVec.ofNat 64 i
  keep : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  cnt : stateAt s.mem (VG.Proof.ChaCha20.X86_64.Xor.st s₀) = ctr (VG.Proof.ChaCha20.X86_64.Xor.S0 s₀) j
  data : ∀ k < VG.Proof.ChaCha20.X86_64.Xor.L s₀, s.mem (VG.Proof.ChaCha20.X86_64.Xor.dp s₀ + BitVec.ofNat 64 k) =
    if k < VG.Proof.ChaCha20.X86_64.Xor.P s₀ j + i then VG.Proof.ChaCha20.X86_64.Xor.D0 s₀ k ^^^ (VG.Proof.ChaCha20.X86_64.Xor.KS s₀).getD k 0 else VG.Proof.ChaCha20.X86_64.Xor.D0 s₀ k
  saved : VG.Proof.ChaCha20.X86_64.Xor.Saved s₀ s.mem
  frame : Frame (VG.Proof.ChaCha20.X86_64.Xor.frameR s₀) s₀.mem s.mem
  ks : ∀ t < 64, s.mem (VG.Proof.ChaCha20.X86_64.Xor.bp s₀ + BitVec.ofNat 64 t) =
    (serialize (Spec.ChaCha20.block (ctr (VG.Proof.ChaCha20.X86_64.Xor.S0 s₀) j))).getD t 0

set_option simprocs false in
theorem sel_ok {s₀ : State} {j : Nat} (hj : VG.Proof.ChaCha20.X86_64.Xor.P s₀ j < VG.Proof.ChaCha20.X86_64.Xor.L s₀) {s : State} (h : VG.Proof.ChaCha20.X86_64.Xor.AInv s₀ j s) :
    WP isa (.seq (.block [.mov .rdx (.reg .r12), .alu .cmp .r12 (.imm 64)])
      (.seq (.ite .b (.block []) (.block [.mov32 .rdx (.imm 64)])) (.block [.mov32 .rcx (.imm 0)])))
      s (VG.Proof.ChaCha20.X86_64.Xor.IInv s₀ j 0) := by
  have h₁ : WP isa (.block [.mov .rdx (.reg .r12), .alu .cmp .r12 (.imm 64)]) s fun s₁ =>
      s₁.gpr .rdx = s.gpr .r12 ∧ (∀ r, r ≠ .rdx → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧
        s₁.mem = s.mem ∧ eval .b s₁ = some (decide (VG.Proof.ChaCha20.X86_64.Xor.L s₀ - VG.Proof.ChaCha20.X86_64.Xor.P s₀ j < 64)) := by
    apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some,
      Option.some.injEq, exists_eq_left', ite_true, ite_false]
    refine ⟨trivial, fun r hr => by simp [hr], trivial, trivial, trivial, ?_⟩
    have se : BitVec.signExtend 64 (64 : BitVec 32) = 64 := by decide
    have hr : (s.gpr .r12).toNat = VG.Proof.ChaCha20.X86_64.Xor.L s₀ - VG.Proof.ChaCha20.X86_64.Xor.P s₀ j := by
      rw [h.r12, VG.Proof.ChaCha20.X86_64.toNat_ofNat_lt (by have := VG.Proof.ChaCha20.X86_64.Xor.L_lt s₀; omega)]
    simp only [eval, se, hr]
    rfl
  have hL := VG.Proof.ChaCha20.X86_64.Xor.L_lt s₀
  have hC : VG.Proof.ChaCha20.X86_64.Xor.C s₀ j = min 64 (VG.Proof.ChaCha20.X86_64.Xor.L s₀ - VG.Proof.ChaCha20.X86_64.Xor.P s₀ j) := rfl
  refine WP.seq (WP.mono h₁ fun s₁ ⟨e₁, e₂, e₃, e₄, e₅, hb⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun s₂ : State => s₂.gpr .rdx = BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Xor.C s₀ j) ∧
      (∀ r, r ≠ .rdx → s₂.gpr r = s₁.gpr r) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr ∧ s₂.mem = s₁.mem) ?_
    fun s₂ ⟨f₁, f₂, f₃, f₄, f₅⟩ => ?_)
  · refine WP.ite _ hb (fun hlt => WP.block_nil (M := isa) ⟨?_, fun _ _ => rfl, rfl, rfl, rfl⟩)
      (fun hge => ?_)
    · simp only [decide_eq_true_eq] at hlt
      rw [e₁, h.r12]; congr 1; omega
    · simp only [decide_eq_false_iff_not, Nat.not_lt] at hge
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, isa, Option.map_some,
        Option.some.injEq, exists_eq_left']
      refine ⟨?_, fun r hr => by simp [State.setReg32, State.setReg, hr], rfl, rfl, rfl⟩
      simp only [State.setReg32, State.setReg, ite_true]
      rw [show VG.Proof.ChaCha20.X86_64.Xor.C s₀ j = 64 by omega]; rfl
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, isa, Option.map_some,
      Option.some.injEq, exists_eq_left']
    have g : ∀ r, r ≠ .rdx → r ≠ .rcx → (s₂.setReg32 .rcx 0).gpr r = s.gpr r := fun r h₁ h₂ => by
      simp only [State.setReg32, State.setReg, h₂, ite_false]; rw [f₂ r h₁, e₂ r h₁]
    have gm : (s₂.setReg32 .rcx 0).mem = s.mem := by rw [State.setReg32, State.setReg]; exact f₅.trans e₅
    refine ⟨by rw [g _ (by decide) (by decide), h.rbx], by rw [g _ (by decide) (by decide), h.rbp],
      by rw [g _ (by decide) (by decide), h.r12], by rw [g _ (by decide) (by decide), h.rsi],
      by simp only [State.setReg32, State.setReg, (by decide : Reg.rdx ≠ .rcx), ite_false]; exact f₁,
      by simp [State.setReg32, State.setReg], fun r hr => ?_, by rw [← h.rd, ← e₃, ← f₃]; rfl,
      by rw [← h.wr, ← e₄, ← f₄]; rfl, by rw [gm]; exact h.cnt, fun k hk => ?_, by rw [gm]; exact h.saved,
      by rw [gm]; exact h.frame, fun t ht => by rw [gm]; exact h.ks t ht⟩
    · have hr' : r ≠ .rdx ∧ r ≠ .rcx := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide
      rw [g r hr'.1 hr'.2]; exact h.keep r hr
    · rw [gm, h.data k hk, Nat.add_zero]

/-! ## One byte -/

def xorBody : List Instr :=
  [.movzx8 .rax dataByte, .movzx8 .r8 ksByte, .alu .xor .rax (.reg .r8), .store8 dataByte .rax,
    .alu .add .rcx (.imm 1), .alu .cmp .rcx (.reg .rdx)]

theorem xorLoop_eq : xorLoop = .loop (.block VG.Proof.ChaCha20.X86_64.Xor.xorBody) .ne := rfl

theorem writeW8_apply (m : Mem) (a x : Addr) (v : Byte) :
    (m.writeW a v) x = if x = a then v else m x := by
  simp only [Mem.writeW, Mem.write]
  by_cases h : x = a
  · subst h; simp
  · have : ¬ (x - a).toNat < 8 / 8 := by
      intro h'
      apply h
      have h0 : (x - a).toNat = 0 := by omega
      have := BitVec.eq_of_toNat_eq (x := x - a) (y := 0) (by rw [h0]; rfl)
      rw [← BitVec.sub_add_cancel x a, this]; exact BitVec.zero_add a
    simp only [this, h, ↓reduceIte]

theorem xor_setWidth (a b : Byte) : (a.setWidth 64 ^^^ b.setWidth 64).setWidth 8 = a ^^^ b := by
  ext i hi; simp

theorem se1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide

/-- Distinct bytes of the data are at distinct addresses. -/
theorem data_ne {s₀ : State} {k k' : Nat} (hk : k < VG.Proof.ChaCha20.X86_64.Xor.L s₀) (hk' : k' < VG.Proof.ChaCha20.X86_64.Xor.L s₀) (h : k' ≠ k) :
    VG.Proof.ChaCha20.X86_64.Xor.dp s₀ + BitVec.ofNat 64 k' ≠ VG.Proof.ChaCha20.X86_64.Xor.dp s₀ + BitVec.ofNat 64 k := by
  have hL := VG.Proof.ChaCha20.X86_64.Xor.L_lt s₀
  intro he
  have e : BitVec.ofNat 64 k' = BitVec.ofNat 64 k := by
    have e := congrArg (· - VG.Proof.ChaCha20.X86_64.Xor.dp s₀) he; simpa using e
  have := congrArg BitVec.toNat e
  rw [VG.Proof.ChaCha20.X86_64.toNat_ofNat_lt (by lit_omega), VG.Proof.ChaCha20.X86_64.toNat_ofNat_lt (by lit_omega)] at this
  exact h this

/-- Byte `k` of the data, before or after block `j`: `P j = 64 j` while blocks remain. -/
theorem P_eq {s₀ : State} {j : Nat} (hj : VG.Proof.ChaCha20.X86_64.Xor.P s₀ j < VG.Proof.ChaCha20.X86_64.Xor.L s₀) : VG.Proof.ChaCha20.X86_64.Xor.P s₀ j = 64 * j := by
  simp only [VG.Proof.ChaCha20.X86_64.Xor.P] at *; omega

theorem ks_eq {s₀ : State} {j i : Nat} (hj : VG.Proof.ChaCha20.X86_64.Xor.P s₀ j < VG.Proof.ChaCha20.X86_64.Xor.L s₀) (hi : i < VG.Proof.ChaCha20.X86_64.Xor.C s₀ j) :
    (VG.Proof.ChaCha20.X86_64.Xor.KS s₀).getD (VG.Proof.ChaCha20.X86_64.Xor.P s₀ j + i) 0 = (serialize (Spec.ChaCha20.block (ctr (VG.Proof.ChaCha20.X86_64.Xor.S0 s₀) j))).getD i 0 := by
  have hP := VG.Proof.ChaCha20.X86_64.Xor.P_eq hj
  have hC : VG.Proof.ChaCha20.X86_64.Xor.C s₀ j = min 64 (VG.Proof.ChaCha20.X86_64.Xor.L s₀ - VG.Proof.ChaCha20.X86_64.Xor.P s₀ j) := rfl
  rw [VG.Proof.ChaCha20.X86_64.Xor.KS, keystream_getD _ (by lit_omega), hP, show (64 * j + i) / 64 = j by omega,
    show (64 * j + i) % 64 = i by omega]

set_option simprocs false in
theorem xor_step {s₀ : State} (hp : VG.Proof.ChaCha20.X86_64.Xor.XPre s₀) {j i : Nat} (hj : VG.Proof.ChaCha20.X86_64.Xor.P s₀ j < VG.Proof.ChaCha20.X86_64.Xor.L s₀) (hi : i < VG.Proof.ChaCha20.X86_64.Xor.C s₀ j)
    {s : State} (h : VG.Proof.ChaCha20.X86_64.Xor.IInv s₀ j i s) :
    WP isa (.block VG.Proof.ChaCha20.X86_64.Xor.xorBody) s fun s' =>
      VG.Proof.ChaCha20.X86_64.Xor.IInv s₀ j (i + 1) s' ∧ s'.zf = some (decide (i + 1 = VG.Proof.ChaCha20.X86_64.Xor.C s₀ j)) := by
  have hL := VG.Proof.ChaCha20.X86_64.Xor.L_lt s₀
  have hk : VG.Proof.ChaCha20.X86_64.Xor.P s₀ j + i < VG.Proof.ChaCha20.X86_64.Xor.L s₀ := by have hC : VG.Proof.ChaCha20.X86_64.Xor.C s₀ j = min 64 (VG.Proof.ChaCha20.X86_64.Xor.L s₀ - VG.Proof.ChaCha20.X86_64.Xor.P s₀ j) := rfl; omega
  have hC64 : VG.Proof.ChaCha20.X86_64.Xor.C s₀ j ≤ 64 := Nat.min_le_left _ _
  have ea₁ : VG.Proof.ChaCha20.X86_64.Xor.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Xor.P s₀ j) + BitVec.ofNat 64 i * BitVec.ofNat 64 1 +
      BitVec.ofInt 64 0 = VG.Proof.ChaCha20.X86_64.Xor.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Xor.P s₀ j + i) := by
    rw [BitVec.mul_one, BitVec.ofNat_add]; simp [BitVec.add_assoc]
  have ea₂ : VG.Proof.ChaCha20.X86_64.Xor.bp s₀ + BitVec.ofNat 64 i * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 =
      VG.Proof.ChaCha20.X86_64.Xor.bp s₀ + BitVec.ofNat 64 i := by simp
  have cd : (VG.Proof.ChaCha20.X86_64.Xor.dR s₀).Contains (VG.Proof.ChaCha20.X86_64.Xor.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Xor.P s₀ j + i)) 1 := VG.Proof.ChaCha20.X86_64.Xor.contains_ofNat (by lit_omega) (by lit_omega)
  have cb : (VG.Proof.ChaCha20.X86_64.Xor.bR s₀).Contains (VG.Proof.ChaCha20.X86_64.Xor.bp s₀ + BitVec.ofNat 64 i) 1 := VG.Proof.ChaCha20.X86_64.Xor.contains_ofNat (by lit_omega) (by lit_omega)
  have i₁ : InRegions (s.rd ++ s.wr) (VG.Proof.ChaCha20.X86_64.Xor.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Xor.P s₀ j + i)) 1 :=
    ⟨VG.Proof.ChaCha20.X86_64.Xor.dR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], cd⟩
  have i₂ : InRegions (s.rd ++ s.wr) (VG.Proof.ChaCha20.X86_64.Xor.bp s₀ + BitVec.ofNat 64 i) 1 :=
    ⟨VG.Proof.ChaCha20.X86_64.Xor.bR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], cb⟩
  have o₁ : InRegions s.wr (VG.Proof.ChaCha20.X86_64.Xor.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Xor.P s₀ j + i)) 1 :=
    ⟨VG.Proof.ChaCha20.X86_64.Xor.dR s₀, by simp [h.wr, hp.wr], cd⟩
  apply WP.of_runBlock
  simp (config := {decide := true}) only [VG.Proof.ChaCha20.X86_64.Xor.xorBody, dataByte, ksByte, runBlock_cons, runStep_some,
    runBlock_nil, exec, State.ea, readSrc, execAlu, arithFlags, State.load8, State.store8,
    State.setReg, State.setFlags, h.rbp, h.rcx, h.rsi, ea₁, ea₂, i₁, i₂, o₁, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', VG.Proof.ChaCha20.X86_64.Xor.se1]
  have hd : s.mem (VG.Proof.ChaCha20.X86_64.Xor.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Xor.P s₀ j + i)) = VG.Proof.ChaCha20.X86_64.Xor.D0 s₀ (VG.Proof.ChaCha20.X86_64.Xor.P s₀ j + i) := by
    rw [h.data _ hk]; simp
  have hks : s.mem (VG.Proof.ChaCha20.X86_64.Xor.bp s₀ + BitVec.ofNat 64 i) = (VG.Proof.ChaCha20.X86_64.Xor.KS s₀).getD (VG.Proof.ChaCha20.X86_64.Xor.P s₀ j + i) 0 := by
    rw [h.ks i (by lit_omega), VG.Proof.ChaCha20.X86_64.Xor.ks_eq hj hi]
  rw [hd, hks, VG.Proof.ChaCha20.X86_64.Xor.xor_setWidth]
  have hfd : Frame [VG.Proof.ChaCha20.X86_64.Xor.dR s₀] s.mem (s.mem.writeW (VG.Proof.ChaCha20.X86_64.Xor.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.X86_64.Xor.P s₀ j + i))
      (VG.Proof.ChaCha20.X86_64.Xor.D0 s₀ (VG.Proof.ChaCha20.X86_64.Xor.P s₀ j + i) ^^^ (VG.Proof.ChaCha20.X86_64.Xor.KS s₀).getD (VG.Proof.ChaCha20.X86_64.Xor.P s₀ j + i) 0)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ cd
  refine ⟨⟨by simp (config := {decide := true}) [h.rbx], by simp (config := {decide := true}) [h.rbp],
    by simp (config := {decide := true}) [h.r12], by simp (config := {decide := true}) [h.rsi],
    by simp (config := {decide := true}) [h.rdx], by simp [BitVec.ofNat_add],
    fun r hr => ?_, h.rd, h.wr, ?_, fun k hk' => ?_, ?_, ?_, fun t ht => ?_⟩, ?_⟩
  · have hr' : r ≠ .rcx ∧ r ≠ .rax ∧ r ≠ .r8 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    simp only [hr'.1, hr'.2.1, hr'.2.2, ite_false]; exact h.keep r hr
  · dsimp only; rw [VG.Proof.ChaCha20.X86_64.Xor.stateAt_frame hfd (by simpa using hp.st_d), h.cnt]
  · dsimp only; rw [VG.Proof.ChaCha20.X86_64.Xor.writeW8_apply]
    by_cases he : k = VG.Proof.ChaCha20.X86_64.Xor.P s₀ j + i
    · subst he; simp
    · simp only [VG.Proof.ChaCha20.X86_64.Xor.data_ne hk hk' he, ite_false]
      rw [h.data k hk']
      by_cases h₁ : k < VG.Proof.ChaCha20.X86_64.Xor.P s₀ j + i
      · simp [h₁, show k < VG.Proof.ChaCha20.X86_64.Xor.P s₀ j + (i + 1) by omega]
      · simp [h₁, show ¬ k < VG.Proof.ChaCha20.X86_64.Xor.P s₀ j + (i + 1) by omega]
  · exact h.saved.frame hfd (by simpa using (hp.d_b.sub_right (VG.Proof.ChaCha20.X86_64.Xor.savR_sub s₀)).symm)
  · exact h.frame.writeW (by simp) _ cd
  · dsimp only; rw [hfd.bytes (R := VG.Proof.ChaCha20.X86_64.Xor.bR s₀) (by simpa using hp.d_b.symm) (show 320 ≤ 2 ^ 64 by omega)
      (show t < 320 by omega)]
    exact h.ks t ht
  · rw [h.rdx, ← Offset.ofNat_sub_ofNat_beq (x := i + 1) (y := VG.Proof.ChaCha20.X86_64.Xor.C s₀ j) (by lit_omega) (by lit_omega),
      BitVec.ofNat_add]
    rfl

/-! ## The end of a block -/

def nextInstrs : List Instr :=
  [.mov32 .rax (.mem (at_ .rbx 48)), .alu32 .add .rax (.imm 1), .store32 (at_ .rbx 48) .rax,
    .alu .add .rbp (.reg .rdx), .alu .sub .r12 (.reg .rdx)]

theorem P_succ {s₀ : State} {j : Nat} (hj : VG.Proof.ChaCha20.X86_64.Xor.P s₀ j < VG.Proof.ChaCha20.X86_64.Xor.L s₀) : VG.Proof.ChaCha20.X86_64.Xor.P s₀ (j + 1) = VG.Proof.ChaCha20.X86_64.Xor.P s₀ j + VG.Proof.ChaCha20.X86_64.Xor.C s₀ j := by
  simp only [VG.Proof.ChaCha20.X86_64.Xor.P, VG.Proof.ChaCha20.X86_64.Xor.C] at *; omega

set_option simprocs false in
theorem next_ok {s₀ : State} (hp : VG.Proof.ChaCha20.X86_64.Xor.XPre s₀) {j : Nat} (hj : VG.Proof.ChaCha20.X86_64.Xor.P s₀ j < VG.Proof.ChaCha20.X86_64.Xor.L s₀) {s : State}
    (h : VG.Proof.ChaCha20.X86_64.Xor.IInv s₀ j (VG.Proof.ChaCha20.X86_64.Xor.C s₀ j) s) :
    WP isa (.block VG.Proof.ChaCha20.X86_64.Xor.nextInstrs) s fun s' =>
      VG.Proof.ChaCha20.X86_64.Xor.OInv s₀ (j + 1) s' ∧ s'.zf = some (decide (VG.Proof.ChaCha20.X86_64.Xor.L s₀ - VG.Proof.ChaCha20.X86_64.Xor.P s₀ (j + 1) = 0)) := by
  have hL := VG.Proof.ChaCha20.X86_64.Xor.L_lt s₀
  have hP := VG.Proof.ChaCha20.X86_64.Xor.P_succ hj
  have hC64 : VG.Proof.ChaCha20.X86_64.Xor.C s₀ j ≤ 64 := Nat.min_le_left _ _
  have hCL : VG.Proof.ChaCha20.X86_64.Xor.C s₀ j ≤ VG.Proof.ChaCha20.X86_64.Xor.L s₀ - VG.Proof.ChaCha20.X86_64.Xor.P s₀ j := Nat.min_le_right _ _
  have c₁ : (VG.Proof.ChaCha20.X86_64.Xor.stR s₀).Contains (VG.Proof.ChaCha20.X86_64.Xor.off (VG.Proof.ChaCha20.X86_64.Xor.st s₀) 48) 4 := VG.Proof.ChaCha20.X86_64.contains_off (by lit_omega) (by lit_omega)
  have i₁ : InRegions (s.rd ++ s.wr) (VG.Proof.ChaCha20.X86_64.Xor.off (VG.Proof.ChaCha20.X86_64.Xor.st s₀) 48) 4 := ⟨VG.Proof.ChaCha20.X86_64.Xor.stR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], c₁⟩
  have o₁ : InRegions s.wr (VG.Proof.ChaCha20.X86_64.Xor.off (VG.Proof.ChaCha20.X86_64.Xor.st s₀) 48) 4 := ⟨VG.Proof.ChaCha20.X86_64.Xor.stR s₀, by simp [h.wr, hp.wr], c₁⟩
  simp only [VG.Proof.ChaCha20.X86_64.Xor.off] at i₁ o₁
  apply WP.of_runBlock
  simp (config := {decide := true}) only [VG.Proof.ChaCha20.X86_64.Xor.nextInstrs, runBlock_cons, runStep_some, runBlock_nil, exec,
    VG.Proof.ChaCha20.X86_64.ea_at, readSrc, readSrc32, execAlu, execAlu32, arithFlags, State.load32, State.store32,
    State.setReg, State.setReg32, State.setFlags, h.rbx, i₁, o₁, ite_true, ite_false, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left', BitVec.setWidth_setWidth_of_le,
    BitVec.setWidth_eq]
  have hv : s.mem.readW (VG.Proof.ChaCha20.X86_64.Xor.st s₀ + BitVec.ofInt 64 ((48 : Nat) : Int)) 32 = (ctr (VG.Proof.ChaCha20.X86_64.Xor.S0 s₀) j)[12]'(by decide) := by
    rw [← h.cnt]; simp [stateAt]
  simp only [hv]
  have hfs : Frame [VG.Proof.ChaCha20.X86_64.Xor.stR s₀] s.mem (s.mem.writeW (VG.Proof.ChaCha20.X86_64.Xor.off (VG.Proof.ChaCha20.X86_64.Xor.st s₀) 48) ((ctr (VG.Proof.ChaCha20.X86_64.Xor.S0 s₀) j)[12]'(by decide) + 1)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₁
  have hr12 : (s.gpr .r12).toNat = VG.Proof.ChaCha20.X86_64.Xor.L s₀ - VG.Proof.ChaCha20.X86_64.Xor.P s₀ j := by rw [h.r12, VG.Proof.ChaCha20.X86_64.toNat_ofNat_lt (by lit_omega)]
  have hrdx : (s.gpr .rdx).toNat = VG.Proof.ChaCha20.X86_64.Xor.C s₀ j := by rw [h.rdx, VG.Proof.ChaCha20.X86_64.toNat_ofNat_lt (by lit_omega)]
  refine ⟨⟨by simp (config := {decide := true}) [h.rbx], ?_, ?_, by simp (config := {decide := true}) [h.rsi],
    fun r hr => ?_, h.rd, h.wr, ?_, fun k hk => ?_, ?_, ?_⟩, ?_⟩
  · simp (config := {decide := true}) only [ite_true, ite_false, h.rbp, h.rdx, hP, BitVec.ofNat_add,
      BitVec.add_assoc]
  · simp (config := {decide := true}) only [ite_true, ite_false]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hr12, hrdx]; omega), hr12, hrdx,
      VG.Proof.ChaCha20.X86_64.toNat_ofNat_lt (by lit_omega)]
    omega
  · have hr' : r ≠ .r12 ∧ r ≠ .rbp ∧ r ≠ .rax := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    simp only [hr'.1, hr'.2.1, hr'.2.2, ite_false]; exact h.keep r hr
  · dsimp only; rw [VG.Proof.ChaCha20.X86_64.Xor.stateAt_writeW_counter, h.cnt, ctr_succ]
  · dsimp only
    rw [hfs.bytes (R := VG.Proof.ChaCha20.X86_64.Xor.dR s₀) (by simpa using hp.st_d.symm) (Nat.le_of_lt (VG.Proof.ChaCha20.X86_64.Xor.L_lt s₀)) hk, h.data k hk, hP]
  · exact h.saved.frame hfs (by simpa using (hp.st_b.sub_right (VG.Proof.ChaCha20.X86_64.Xor.savR_sub s₀)).symm)
  · exact h.frame.writeW (by simp) _ c₁
  · have hz : (s.gpr .r12 - s.gpr .rdx == 0) = decide (VG.Proof.ChaCha20.X86_64.Xor.L s₀ - VG.Proof.ChaCha20.X86_64.Xor.P s₀ j - VG.Proof.ChaCha20.X86_64.Xor.C s₀ j = 0) := by
      rw [h.r12, h.rdx, Offset.ofNat_sub_ofNat_beq (by lit_omega) (by lit_omega)]
      exact decide_eq_decide.mpr (by lit_omega)
    rw [hz, hP, Nat.sub_sub]

/-! ## A whole block -/

theorem xorLoop_ok {s₀ : State} (hp : VG.Proof.ChaCha20.X86_64.Xor.XPre s₀) {j : Nat} (hj : VG.Proof.ChaCha20.X86_64.Xor.P s₀ j < VG.Proof.ChaCha20.X86_64.Xor.L s₀) {s : State}
    (h : VG.Proof.ChaCha20.X86_64.Xor.IInv s₀ j 0 s) : WP isa xorLoop s (VG.Proof.ChaCha20.X86_64.Xor.IInv s₀ j (VG.Proof.ChaCha20.X86_64.Xor.C s₀ j)) := by
  have hpos : 0 < VG.Proof.ChaCha20.X86_64.Xor.C s₀ j := by simp only [VG.Proof.ChaCha20.X86_64.Xor.C]; omega
  rw [VG.Proof.ChaCha20.X86_64.Xor.xorLoop_eq]
  let Inv : Nat → State → Prop := fun n s => ∃ i, n = VG.Proof.ChaCha20.X86_64.Xor.C s₀ j - i ∧ i < VG.Proof.ChaCha20.X86_64.Xor.C s₀ j ∧ VG.Proof.ChaCha20.X86_64.Xor.IInv s₀ j i s
  have hstep : ∀ n s, Inv n s → WP isa (.block VG.Proof.ChaCha20.X86_64.Xor.xorBody) s (fun s' =>
      (eval .ne s' = some false ∧ VG.Proof.ChaCha20.X86_64.Xor.IInv s₀ j (VG.Proof.ChaCha20.X86_64.Xor.C s₀ j) s') ∨ (eval .ne s' = some true ∧ ∃ n' < n, Inv n' s')) := by
    rintro n s ⟨i, rfl, hi, hI⟩
    refine WP.mono (VG.Proof.ChaCha20.X86_64.Xor.xor_step hp hj hi hI) fun s' ⟨h', hz⟩ => ?_
    by_cases hl : i + 1 = VG.Proof.ChaCha20.X86_64.Xor.C s₀ j
    · exact .inl ⟨by simp [eval, hz, hl], hl ▸ h'⟩
    · exact .inr ⟨by simp [eval, hz, hl], VG.Proof.ChaCha20.X86_64.Xor.C s₀ j - (i + 1), by omega, i + 1, rfl, by omega, h'⟩
  exact WP.loop (M := isa) Inv hstep (VG.Proof.ChaCha20.X86_64.Xor.C s₀ j) s ⟨0, by simp, hpos, h⟩

theorem body_eq : body =
    .seq (.block [.mov .rdi (.reg .rbx)]) (.seq (.call "vg_chacha20_block" Impl.ChaCha20.X86_64.block)
    (.seq (.block [.mov .rdx (.reg .r12), .alu .cmp .r12 (.imm 64)])
    (.seq (.ite .b (.block []) (.block [.mov32 .rdx (.imm 64)]))
    (.seq (.block [.mov32 .rcx (.imm 0)]) (.seq xorLoop (.block VG.Proof.ChaCha20.X86_64.Xor.nextInstrs)))))) := rfl

theorem body_ok {s₀ : State} (hp : VG.Proof.ChaCha20.X86_64.Xor.XPre s₀) {j : Nat} (hj : VG.Proof.ChaCha20.X86_64.Xor.P s₀ j < VG.Proof.ChaCha20.X86_64.Xor.L s₀) {s : State}
    (h : VG.Proof.ChaCha20.X86_64.Xor.OInv s₀ j s) :
    WP isa body s fun s' => VG.Proof.ChaCha20.X86_64.Xor.OInv s₀ (j + 1) s' ∧ s'.zf = some (decide (VG.Proof.ChaCha20.X86_64.Xor.L s₀ - VG.Proof.ChaCha20.X86_64.Xor.P s₀ (j + 1) = 0)) := by
  have hc := VG.Proof.ChaCha20.X86_64.Xor.call_ok hp h
  rw [WP.seq_iff] at hc
  rw [VG.Proof.ChaCha20.X86_64.Xor.body_eq, WP.seq_iff]
  refine WP.mono hc fun s₁ h₁ => ?_
  rw [WP.seq_iff]
  refine WP.mono h₁ fun s₂ h₂ => ?_
  have hs := VG.Proof.ChaCha20.X86_64.Xor.sel_ok hj h₂
  rw [WP.seq_iff] at hs
  rw [WP.seq_iff]
  refine WP.mono hs fun s₃ h₃ => ?_
  rw [WP.seq_iff] at h₃
  rw [WP.seq_iff]
  refine WP.mono h₃ fun s₄ h₄ => ?_
  rw [WP.seq_iff]
  refine WP.mono h₄ fun s₅ h₅ => ?_
  exact WP.seq (WP.mono (VG.Proof.ChaCha20.X86_64.Xor.xorLoop_ok hp hj h₅) fun s₆ h₆ => VG.Proof.ChaCha20.X86_64.Xor.next_ok hp hj h₆)

/-! ## The epilogue -/

theorem ret_stack (s₀ : State) : (VG.Proof.ChaCha20.X86_64.Xor.retR s₀).Disjoint (VG.Proof.ChaCha20.X86_64.Xor.stackR s₀) := by
  have := Offset.disjoint_base (s₀.gpr .rsp - BitVec.ofNat 64 8) (d := 8) (n := 8) (k := 8) (by decide) (by decide)
  rwa [BitVec.sub_add_cancel] at this

theorem epilogue_ok {s₀ : State} (hp : VG.Proof.ChaCha20.X86_64.Xor.XPre s₀) {j : Nat} (hj : VG.Proof.ChaCha20.X86_64.Xor.P s₀ j = VG.Proof.ChaCha20.X86_64.Xor.L s₀) {s : State}
    (h : VG.Proof.ChaCha20.X86_64.Xor.OInv s₀ j s) :
    WP isa (.block restore) s fun s' =>
      (gprPreserved s₀ s' ∧ Proof.ChaCha20.xorX86_64.post s₀ s') ∧ s'.gpr .rsi = VG.Proof.ChaCha20.X86_64.Xor.bp s₀ := by
  refine WP.mono (Spill.restore_ok .rsi saved s₀.gpr s (by decide) (fun p hp' => ?_)
    (by rw [h.rsi]; exact h.saved)) fun s' ⟨h₁, h₂, hm, _⟩ => ?_
  · have := VG.Proof.ChaCha20.X86_64.Xor.saved_bound p hp'
    rw [h.rsi]
    exact ⟨VG.Proof.ChaCha20.X86_64.Xor.bR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], Offset.contains_base _ (by omega) (by lit_omega)⟩
  refine ⟨⟨⟨fun r hr => ?_, ?_⟩, ?_⟩, by rw [h₂ _ (by decide), h.rsi]⟩
  · by_cases hs : r ∈ saved.map Prod.fst
    · exact h₁ r hs
    · rw [h₂ r hs]
      revert hs; revert r; exact fun r hr hs => h.keep r (by revert r hr; decide)
  · show s'.mem.readW _ _ = _
    rw [hm]
    refine h.frame.readW (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.ret_st
    · exact hp.ret_d
    · exact hp.ret_b
    · exact VG.Proof.ChaCha20.X86_64.Xor.ret_stack s₀
  · show bytesAt s'.mem _ _ = _
    rw [hm]
    refine bytesAt_xor (length_keystream _ _) fun k hk => ?_
    have hk' : k < VG.Proof.ChaCha20.X86_64.Xor.L s₀ := hk
    rw [h.data k hk']
    simp only [show k < VG.Proof.ChaCha20.X86_64.Xor.P s₀ j by omega, ite_true]

/-! ## The whole function -/

theorem xor_eq : Impl.ChaCha20.X86_64.Xor.xor =
    .seq (.block (save ++ ([.mov .rbx (.reg .rdi), .mov .rbp (.reg .rsi), .mov .r12 (.reg .rdx),
      .mov .rsi (.reg .rcx), .alu .test .r12 (.reg .r12)] : List Instr)))
    (.seq (.ite .e (.block []) (.loop body .ne)) (.block restore)) := rfl

theorem correct {s₀ : State} (hp : VG.Proof.ChaCha20.X86_64.Xor.XPre s₀) :
    WP isa Impl.ChaCha20.X86_64.Xor.xor s₀ fun s' =>
      (gprPreserved s₀ s' ∧ Proof.ChaCha20.xorX86_64.post s₀ s') ∧ s'.gpr .rsi = VG.Proof.ChaCha20.X86_64.Xor.bp s₀ := by
  rw [VG.Proof.ChaCha20.X86_64.Xor.xor_eq]
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86_64.Xor.prologue_ok hp) fun s₁ ⟨h₁, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ j, VG.Proof.ChaCha20.X86_64.Xor.P s₀ j = VG.Proof.ChaCha20.X86_64.Xor.L s₀ ∧ VG.Proof.ChaCha20.X86_64.Xor.OInv s₀ j s) ?_
    fun s₂ ⟨j, hj, h₂⟩ => VG.Proof.ChaCha20.X86_64.Xor.epilogue_ok hp hj h₂)
  refine WP.ite (decide (VG.Proof.ChaCha20.X86_64.Xor.L s₀ = 0)) (by simp [eval, hz]) (fun h => ?_) (fun h => ?_)
  · simp only [decide_eq_true_eq] at h
    exact WP.block_nil (M := isa) ⟨0, by simp [VG.Proof.ChaCha20.X86_64.Xor.P, h], h₁⟩
  · simp only [decide_eq_false_iff_not] at h
    let Inv : Nat → State → Prop := fun n s => ∃ j, n = VG.Proof.ChaCha20.X86_64.Xor.L s₀ - VG.Proof.ChaCha20.X86_64.Xor.P s₀ j ∧ VG.Proof.ChaCha20.X86_64.Xor.P s₀ j < VG.Proof.ChaCha20.X86_64.Xor.L s₀ ∧ VG.Proof.ChaCha20.X86_64.Xor.OInv s₀ j s
    have hstep : ∀ n s, Inv n s → WP isa body s (fun s' =>
        (eval .ne s' = some false ∧ ∃ j, VG.Proof.ChaCha20.X86_64.Xor.P s₀ j = VG.Proof.ChaCha20.X86_64.Xor.L s₀ ∧ VG.Proof.ChaCha20.X86_64.Xor.OInv s₀ j s') ∨
        (eval .ne s' = some true ∧ ∃ n' < n, Inv n' s')) := by
      rintro n s ⟨j, rfl, hj, hI⟩
      refine WP.mono (VG.Proof.ChaCha20.X86_64.Xor.body_ok hp hj hI) fun s' ⟨h', hz'⟩ => ?_
      have hP := VG.Proof.ChaCha20.X86_64.Xor.P_succ hj
      have hC : 0 < VG.Proof.ChaCha20.X86_64.Xor.C s₀ j := by simp only [VG.Proof.ChaCha20.X86_64.Xor.C]; omega
      have hle : VG.Proof.ChaCha20.X86_64.Xor.P s₀ (j + 1) ≤ VG.Proof.ChaCha20.X86_64.Xor.L s₀ := by simp only [VG.Proof.ChaCha20.X86_64.Xor.P]; omega
      by_cases hl : VG.Proof.ChaCha20.X86_64.Xor.L s₀ - VG.Proof.ChaCha20.X86_64.Xor.P s₀ (j + 1) = 0
      · exact .inl ⟨by simp [eval, hz', hl], j + 1, by omega, h'⟩
      · exact .inr ⟨by simp [eval, hz', hl], VG.Proof.ChaCha20.X86_64.Xor.L s₀ - VG.Proof.ChaCha20.X86_64.Xor.P s₀ (j + 1), by omega, j + 1, rfl, by omega, h'⟩
    exact WP.loop (M := isa) Inv hstep (VG.Proof.ChaCha20.X86_64.Xor.L s₀ - VG.Proof.ChaCha20.X86_64.Xor.P s₀ 0) s₁ ⟨0, rfl, by simp [VG.Proof.ChaCha20.X86_64.Xor.P]; omega, h₁⟩

/-- `vg_chacha20_xor` returns with `rsi` pointing at `buf`, for a caller that
recomputes pointers from it. -/
theorem xor_rsi (s : State) (hs : Proof.ChaCha20.xorX86_64.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20.X86_64.Xor.xor s t s' ∧ abiPreserved s s' ∧
      (Proof.ChaCha20.xorX86_64.post s s' ∧ s'.gpr .rsi = s.gpr .rcx) := by
  obtain ⟨t, s', he, ⟨h, hr⟩⟩ := VG.Proof.ChaCha20.X86_64.Xor.correct (XPre.of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2, hr⟩

/-! ## Constant time -/

/-- The public registers and what is known about memory on entry: the lengths
of `state` and `buf` (the data's varies) and the registers holding their bases. -/
def τ₀ : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .rsp], flags := false, lens := [64, 0, 320],
    bases := [(.rdi, 0, 0), (.rsi, 1, 0), (.rcx, 2, 0)] }

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.ChaCha20.xorX86_64.pre s₁)
    (h₂ : Proof.ChaCha20.xorX86_64.pre s₂) (hpub : Proof.ChaCha20.xorX86_64.pub s₁ s₂) :
    X86_64.Taint.Agree VG.Proof.ChaCha20.X86_64.Xor.τ₀ s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := hpub
  have wf : ∀ s, Proof.ChaCha20.xorX86_64.pre s → X86_64.Taint.Wf VG.Proof.ChaCha20.X86_64.Xor.τ₀ s := by
    intro s hs
    obtain ⟨-, hw, d1, d2, d3, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, VG.Proof.ChaCha20.X86_64.Xor.τ₀], by simp [hw, d1, d2, d3], by simp [hw, Nat.le_of_lt (s.gpr .rdx).isLt]⟩,
      fun p hp => ?_⟩
    simp only [VG.Proof.ChaCha20.X86_64.Xor.τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    X86_64.Taint.noLo⟩
  · simp only [VG.Proof.ChaCha20.X86_64.Xor.τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [h₁.2.1, h₂.2.1, p1, p2, p3, p4]
  · intro sl h; simp [VG.Proof.ChaCha20.X86_64.Xor.τ₀] at h
  · intro sl h; simp [VG.Proof.ChaCha20.X86_64.Xor.τ₀] at h

/-- A state satisfying the precondition (with no data). -/
def sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rcx => 0x3000 | .rsp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 0⟩, ⟨0x3000, 320⟩]

theorem xor_correct (s : State) (hs : Proof.ChaCha20.xorX86_64.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20.X86_64.Xor.xor s t s' ∧ abiPreserved s s' ∧
      Proof.ChaCha20.xorX86_64.post s s' :=
  (VG.Proof.ChaCha20.X86_64.Xor.xor_rsi s hs).imp fun _ ⟨s', he, ha, h, _⟩ => ⟨s', he, ha, h⟩

theorem xor_ct : ConstantTime isa Proof.ChaCha20.xorX86_64.pre Proof.ChaCha20.xorX86_64.pub
    Impl.ChaCha20.X86_64.Xor.xor :=
  VG.Taint.constantTime (A := taint) VG.Proof.ChaCha20.X86_64.Xor.τ₀ (fun _ _ h₁ h₂ hp => VG.Proof.ChaCha20.X86_64.Xor.agree₀ h₁ h₂ hp) (by taint_decide)

theorem xor_verified :
    Verified X86_64.target Impl.ChaCha20.X86_64.Xor.xor (Spec.ChaCha20.xorContract X86_64.abi 8) :=
  Verified.of_correct VG.Proof.ChaCha20.X86_64.Xor.xor_correct VG.Proof.ChaCha20.X86_64.Xor.xor_ct
    (by sig_implies [Spec.ChaCha20.xorContract, Spec.ChaCha20.xorSig, X86_64.abi, X86_64.argRegs,
      Proof.ChaCha20.xorX86_64]
      [sat] using VG.Proof.ChaCha20.X86_64.Xor.sat)

end VG.Proof.ChaCha20.X86_64.Xor

end

module

public import VerifiedGarbage.Proof.Sha512.X86_64.Avx512.Compress
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Spec
import VerifiedGarbage.Proof.Sha512.X86_64.Avx512.Lit
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-!
# SHA-512 with AVX-512VL on x86-64: two compressions at once

`Impl.Sha512.X86_64.Avx512.compress2`: each `xmm` register holds a value of
the first compression in quadword 0 and of the second in quadword 1, and
every instruction of a round acts on the two alike.
-/

@[expose] public section

namespace VG.Proof.Sha512.X86_64.Avx512

open VG VG.X86_64 VG.Impl.Sha512.X86_64.Avx512
open VG.Proof.Sha512.X86_64.Avx2 (qword_append_0 qword_append_1 paddq_eq psrlq_eq)
open VG.Spec.Sha512 (HashValue Word Block K W bsig0 bsig1 ch maj ssig0 ssig1)
open VG.Proof.Sha512.X86_64 (ofInt_natCast contains_offset)
open VG.Proof.Sha512 (roundKW rounds_succ round_eq roundKW_0 roundKW_1 roundKW_2 roundKW_3 roundKW_4 roundKW_5
  roundKW_6 roundKW_7)

/-! ## `vpternlogd`, on quadwords -/

/-- `0xCA`: the bits of the second where the first has a one, of the third
where it has a zero. -/
theorem ternCA (a b c : BitVec 128) : ternlog a b c 0xCA = (a &&& b) ^^^ (~~~a &&& c) := by
  simp only [ternlog, List.range, List.range.loop, List.foldl,
    show (0xCA : BitVec 8).getLsbD 0 = false from rfl, show (0xCA : BitVec 8).getLsbD 1 = true from rfl,
    show (0xCA : BitVec 8).getLsbD 2 = false from rfl, show (0xCA : BitVec 8).getLsbD 3 = true from rfl,
    show (0xCA : BitVec 8).getLsbD 4 = false from rfl, show (0xCA : BitVec 8).getLsbD 5 = false from rfl,
    show (0xCA : BitVec 8).getLsbD 6 = true from rfl, show (0xCA : BitVec 8).getLsbD 7 = true from rfl,
    Nat.testBit, Nat.reduceShiftRight, Nat.reduceAnd, Nat.reduceBNe, Bool.false_eq_true, ↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_not,
    show (0 : BitVec 128).getLsbD j = false from BitVec.getLsbD_zero, hj, decide_true, Bool.true_and]
  generalize a.getLsbD j = x; generalize b.getLsbD j = y; generalize c.getLsbD j = z
  revert x y z; decide

/-- `0xE8`: the majority. -/
theorem ternE8 (a b c : BitVec 128) : ternlog a b c 0xE8 = (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c) := by
  simp only [ternlog, List.range, List.range.loop, List.foldl,
    show (0xE8 : BitVec 8).getLsbD 0 = false from rfl, show (0xE8 : BitVec 8).getLsbD 1 = false from rfl,
    show (0xE8 : BitVec 8).getLsbD 2 = false from rfl, show (0xE8 : BitVec 8).getLsbD 3 = true from rfl,
    show (0xE8 : BitVec 8).getLsbD 4 = false from rfl, show (0xE8 : BitVec 8).getLsbD 5 = true from rfl,
    show (0xE8 : BitVec 8).getLsbD 6 = true from rfl, show (0xE8 : BitVec 8).getLsbD 7 = true from rfl,
    Nat.testBit, Nat.reduceShiftRight, Nat.reduceAnd, Nat.reduceBNe, Bool.false_eq_true, ↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_not,
    show (0 : BitVec 128).getLsbD j = false from BitVec.getLsbD_zero, hj, decide_true, Bool.true_and]
  generalize a.getLsbD j = x; generalize b.getLsbD j = y; generalize c.getLsbD j = z
  revert x y z; decide

theorem ternCA_eq (a b c d e f : Word) :
    ternlog (a ++ b) (c ++ d) (e ++ f) 0xCA = ch a c e ++ ch b d f := by
  rw [ternCA, BitVec.and_append, BitVec.not_append, BitVec.and_append, BitVec.xor_append]; rfl

theorem ternE8_eq (a b c d e f : Word) :
    ternlog (a ++ b) (c ++ d) (e ++ f) 0xE8 = maj a c e ++ maj b d f := by
  rw [ternE8, BitVec.and_append, BitVec.and_append, BitVec.and_append, BitVec.xor_append, BitVec.xor_append]; rfl

/-! ## A round -/

/-- The working variables of both compressions, `v₀` and `v₁`, are in the
registers of round `t`. -/
def Vars2 (t : Nat) (s : State) (v₀ v₁ : HashValue) : Prop :=
  s.xmm (sv t 0) = v₁[0] ++ v₀[0] ∧ s.xmm (sv t 1) = v₁[1] ++ v₀[1] ∧ s.xmm (sv t 2) = v₁[2] ++ v₀[2] ∧
  s.xmm (sv t 3) = v₁[3] ++ v₀[3] ∧ s.xmm (sv t 4) = v₁[4] ++ v₀[4] ∧ s.xmm (sv t 5) = v₁[5] ++ v₀[5] ∧
  s.xmm (sv t 6) = v₁[6] ++ v₀[6] ∧ s.xmm (sv t 7) = v₁[7] ++ v₀[7]

theorem sv_succ (t k : Nat) (hk : k < 7) : sv (t + 1) (k + 1) = sv t k := by
  simp only [sv]; congr 1; omega

theorem sv_succ_zero (t : Nat) : sv (t + 1) 0 = sv t 7 := by
  simp only [sv]; congr 1; omega

/-- The registers of a round are all different. -/
theorem round2_nodup (t : Nat) :
    [sv t 0, sv t 1, sv t 2, sv t 3, sv t 4, sv t 5, sv t 6, sv t 7, u0, u1, u2, w0, w1, mB].Nodup := by
  simp only [sv]
  have h8 := Nat.mod_lt t (show 8 > 0 by omega)
  generalize t % 8 = c at *
  revert h8; revert c; decide +kernel

/-- What a round leaves alone: all but the working variables and its
temporaries. -/
def Keeps2 (s s' : State) : Prop :=
  s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr = s.gpr ∧
    (∀ r, r = w0 ∨ r = w1 ∨ r = mB → s'.xmm r = s.xmm r ∧ s'.ymmHi r = s.ymmHi r)

/-- `T₁`, as the round adds it up. -/
theorem t1_order2 (h e f g k w : Word) :
    h + (w + k) + ((e.rotateRight 14 ^^^ e.rotateRight 18 ^^^ e.rotateRight 41) + ch e f g) =
      h + bsig1 e + ch e f g + k + w := by
  rw [show bsig1 e = e.rotateRight 14 ^^^ e.rotateRight 18 ^^^ e.rotateRight 41 from rfl]; ac_rfl

/-- `T₁ + T₂`, as the round adds it up. -/
theorem t2_order2 (t a b c : Word) :
    t + (a.rotateRight 28 ^^^ a.rotateRight 34 ^^^ a.rotateRight 39) + maj a b c = t + (bsig0 a + maj a b c) := by
  rw [BitVec.add_assoc]; rfl

/-- The round is symbolically executed once, for any registers `a … h`,
with `Wₜ + Kₜ` of both in `kw`. -/
theorem round2_ok (t : Nat) (kw : XReg) (hkw : kw = w0 ∨ kw = w1) (s : State) (v₀ v₁ : HashValue)
    (k x₀ x₁ : Word) (hv : Vars2 t s v₀ v₁) (hx : s.xmm kw = (x₁ + k) ++ (x₀ + k)) :
    WP isa (.block (round2 t kw)) s fun s' =>
      Vars2 (t + 1) s' (roundKW v₀ k x₀) (roundKW v₁ k x₁) ∧ Keeps2 s s' := by
  unfold Keeps2
  have hd := round2_nodup t
  have hd' := VG.nodup_reverse hd
  apply WP.of_runBlock
  simp only [Vars2, sv_succ_zero, sv_succ t _ (show 0 < 7 by omega),
    sv_succ t _ (show 1 < 7 by omega), sv_succ t _ (show 2 < 7 by omega),
    sv_succ t _ (show 3 < 7 by omega), sv_succ t _ (show 4 < 7 by omega),
    sv_succ t _ (show 5 < 7 by omega), sv_succ t _ (show 6 < 7 by omega)] at hv ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hv
  simp only [round2, xb, xror, xtern]
  generalize sv t 0 = a at *
  generalize sv t 1 = b at *
  generalize sv t 2 = c at *
  generalize sv t 3 = d at *
  generalize sv t 4 = e at *
  generalize sv t 5 = f at *
  generalize sv t 6 = g at *
  generalize sv t 7 = h at *
  simp only [u0, u1, u2, w0, w1, mB, List.nodup_cons, List.mem_cons, List.not_mem_nil, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, or_false, not_or,
    List.nodup_nil, and_true] at hd hd' hkw ⊢
  rcases hkw with rfl | rfl <;>
  · simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, reduceExec,
      reduceVOpExec, isa, RegUpd.xmm_setV, RegUpd.ymmHi_setV_128, RegUpd.gpr_setV, RegUpd.mem_setV,
      RegUpd.rd_setV, RegUpd.wr_setV, State.lane, hd, hd', h0, h1, h2, h3, h4, h5, h6, h7, hx,
      Option.some.injEq, exists_eq_left', paddq_eq, ror_eq, tern96_eq, ternCA_eq, ternE8_eq,
      reduceVBinOpSse, BitVec.reduceToNat, Nat.reduceMod]
    simp only [roundKW_0, roundKW_1, roundKW_2, roundKW_3, roundKW_4, roundKW_5, roundKW_6, roundKW_7,
      t1_order2, t2_order2, and_self, true_and]
    intro r hr
    rcases hr with rfl | rfl | rfl <;> simp [hd']

/-! ## The round constants -/

theorem flatMap_dup_getD (l : List Word) (t q : Nat) (hq : q < 2) :
    (l.flatMap fun k => [k, k]).getD (2 * t + q) 0 = l.getD t 0 := by
  induction l generalizing t with
  | nil => simp
  | cons a l ih =>
    cases t with
    | zero => rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl <;> simp
    | succ t =>
      rw [show 2 * (t + 1) + q = (2 * t + q) + 2 by omega]
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.getD_cons_succ]
      exact ih t

/-- Words `2t` and `2t+1` of the table are `Kₜ`. -/
theorem Ks2_getD (t : Nat) {q : Nat} (hq : q < 2) : Ks2.getD (2 * t + q) 0 = K t :=
  flatMap_dup_getD _ t q hq

theorem flatMap_dup_length (l : List Word) : (l.flatMap fun k => [k, k]).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]; omega

theorem Ks2_length : Ks2.length = 160 := by
  rw [Ks2, flatMap_dup_length, show Spec.Sha512.Ks.length = 80 from rfl]

/-- The index of iteration `j`. -/
abbrev idx2 (j : Nat) : BitVec 64 := BitVec.ofNat 64 (256 * j)

theorem kSlot_ea (s : State) {j : Nat} (h : s.gpr .r9 = idx2 j) (i : Nat) :
    s.ea (kSlot i) = s.gpr .rax + BitVec.ofNat 64 (8 * (4 * (8 * j + i))) := by
  simp only [State.ea, kSlot, h, ofInt_natCast, BitVec.mul_one]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 256 * j + 32 * i = 8 * (4 * (8 * j + i)) by omega]

/-- The table's base register holds its address, and step `i` of iteration
`j` reads `Kₜ` and `Kₜ₊₁` (`t = 16 j + 2 i`), each twice. -/
theorem exec_kSlot2 (s : State) {j : Nat} (i : Nat) (h9 : s.gpr .r9 = idx2 j)
    (hb : s.gpr .rax = s.syms kSym) (hn : 8 * j + i < 40) :
    X86_64.exec (.vmovdquTbl w1 (kSlot i) kSym Ks2) s =
      some (s.setV .l256 w1 (K (16 * j + 2 * i) ++ K (16 * j + 2 * i))
        (K (16 * j + 2 * i + 1) ++ K (16 * j + 2 * i + 1))) := by
  have e : s.ea (kSlot i) - s.syms kSym = BitVec.ofNat 64 (8 * (4 * (8 * j + i))) := by
    rw [kSlot_ea s h9, hb, BitVec.add_comm, BitVec.add_sub_cancel]
  have e' : (BitVec.ofNat 64 (8 * (4 * (8 * j + i)))).toNat = 8 * (4 * (8 * j + i)) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hl : 4 * (8 * j + i) + 4 ≤ Ks2.length := by rw [Ks2_length]; omega
  have g0 : Ks2.getD (4 * (8 * j + i) + 0) 0 = K (16 * j + 2 * i) := by
    rw [show 4 * (8 * j + i) + 0 = 2 * (16 * j + 2 * i) + 0 by omega, Ks2_getD _ (by omega)]
  have g1 : Ks2.getD (4 * (8 * j + i) + 1) 0 = K (16 * j + 2 * i) := by
    rw [show 4 * (8 * j + i) + 1 = 2 * (16 * j + 2 * i) + 1 by omega, Ks2_getD _ (by omega)]
  have g2 : Ks2.getD (4 * (8 * j + i) + 2) 0 = K (16 * j + 2 * i + 1) := by
    rw [show 4 * (8 * j + i) + 2 = 2 * (16 * j + 2 * i + 1) + 0 by omega, Ks2_getD _ (by omega)]
  have g3 : Ks2.getD (4 * (8 * j + i) + 3) 0 = K (16 * j + 2 * i + 1) := by
    rw [show 4 * (8 * j + i) + 3 = 2 * (16 * j + 2 * i + 1) + 1 by omega, Ks2_getD _ (by omega)]
  simp only [X86_64.exec, e, e', show (kSlot i).base = .rax from rfl, hb, Nat.mul_mod_right,
    Nat.mul_div_right (4 * (8 * j + i)) (by decide : 0 < 8), hl, and_self, ↓reduceIte, g0, g1, g2, g3]

/-! ## Two rounds from their words -/

/-- The round constants of step `i` of iteration `j`, added to its words. -/
theorem kw_ok (s : State) {j : Nat} (i : Nat) (h9 : s.gpr .r9 = idx2 j) (hb : s.gpr .rax = s.syms kSym)
    (hn : 8 * j + i < 40) (a₀ a₁ b₀ b₁ : Word) (ha : s.xmm w0 = a₁ ++ a₀) (hbb : s.ymmHi w0 = b₁ ++ b₀) :
    WP isa (.block [.vmovdquTbl w1 (kSlot i) kSym Ks2, .vop (.vbin .vpaddq .l256 w0 w0 w1),
      .vop (.vextracti128 w1 w0 1)]) s fun s' =>
      s'.xmm w0 = (a₁ + K (16 * j + 2 * i)) ++ (a₀ + K (16 * j + 2 * i)) ∧
      s'.xmm w1 = (b₁ + K (16 * j + 2 * i + 1)) ++ (b₀ + K (16 * j + 2 * i + 1)) ∧
      (∀ r, r ≠ w0 → r ≠ w1 → s'.xmm r = s.xmm r ∧ s'.ymmHi r = s.ymmHi r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  rw [runBlock_cons, exec_kSlot2 s i h9 hb hn]
  simp only [w0] at ha hbb
  simp only [w0, w1, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, reduceExec,
    reduceVOpExec, isa, RegUpd.xmm_setV, RegUpd.ymmHi_setV_256, RegUpd.ymmHi_setV_128, RegUpd.gpr_setV,
    RegUpd.mem_setV, RegUpd.rd_setV, RegUpd.wr_setV, State.lane, ha, hbb, Option.some.injEq,
    exists_eq_left', paddq_eq, reduceVBinOpSse, show (1 : BitVec 8).getLsbD 0 = true from rfl]
  exact ⟨trivial, trivial, fun r h0 h1 => by simp [h0, h1], trivial, trivial, trivial, trivial⟩

theorem sv_add16 (j t k : Nat) : sv (16 * j + t) k = sv t k := by
  simp only [sv]; congr 1; omega

theorem vars2_add16 (j t : Nat) (s : State) (v₀ v₁ : HashValue) : Vars2 (16 * j + t) s v₀ v₁ ↔ Vars2 t s v₀ v₁ := by
  simp only [Vars2, sv_add16]

/-- A working variable's register is neither `w0` nor `w1`. -/
theorem sv_ne (t k : Nat) : sv t k ≠ w0 ∧ sv t k ≠ w1 := by
  simp only [sv]
  have h8 := Nat.mod_lt (k + 8 - t % 8) (show 8 > 0 by omega)
  generalize (k + 8 - t % 8) % 8 = c at *
  revert h8; revert c; decide

theorem sv_ne' (t k : Nat) : sv t k ≠ u0 ∧ sv t k ≠ u1 := by
  simp only [sv]
  have h8 := Nat.mod_lt (k + 8 - t % 8) (show 8 > 0 by omega)
  generalize (k + 8 - t % 8) % 8 = c at *
  revert h8; revert c; decide

/-- The working variables, when their registers are kept. -/
theorem Vars2.of_xmm {t : Nat} {s s' : State} {v₀ v₁ : HashValue} (h : Vars2 t s v₀ v₁)
    (hx : ∀ r, r ≠ w0 → r ≠ w1 → s'.xmm r = s.xmm r) : Vars2 t s' v₀ v₁ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨(hx _ (sv_ne t 0).1 (sv_ne t 0).2).trans h0, (hx _ (sv_ne t 1).1 (sv_ne t 1).2).trans h1,
    (hx _ (sv_ne t 2).1 (sv_ne t 2).2).trans h2, (hx _ (sv_ne t 3).1 (sv_ne t 3).2).trans h3,
    (hx _ (sv_ne t 4).1 (sv_ne t 4).2).trans h4, (hx _ (sv_ne t 5).1 (sv_ne t 5).2).trans h5,
    (hx _ (sv_ne t 6).1 (sv_ne t 6).2).trans h6, (hx _ (sv_ne t 7).1 (sv_ne t 7).2).trans h7⟩

/-- What the steps keep: the pointers and the index, the memory, and the
`pshufb` mask. -/
def Kept (s s' : State) : Prop :=
  s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
    s'.xmm mB = s.xmm mB ∧ s'.ymmHi mB = s.ymmHi mB

/-- Rounds `t` and `t + 1` (`t = 16 j + 2 i`) of both, from their words in `w0`. -/
theorem rounds2_ok (s : State) {j : Nat} (i : Nat) (hn : 8 * j + i < 40) (H₀ H₁ : HashValue) (M₀ M₁ : Block)
    (h9 : s.gpr .r9 = idx2 j) (hb : s.gpr .rax = s.syms kSym)
    (hv : Vars2 (2 * i) s (Spec.Sha512.rounds H₀ M₀ (16 * j + 2 * i)) (Spec.Sha512.rounds H₁ M₁ (16 * j + 2 * i)))
    (ha : s.xmm w0 = W M₁ (16 * j + 2 * i) ++ W M₀ (16 * j + 2 * i))
    (hbb : s.ymmHi w0 = W M₁ (16 * j + 2 * i + 1) ++ W M₀ (16 * j + 2 * i + 1)) :
    WP isa (.block (rounds2 i)) s fun s' =>
      Vars2 (2 * i + 2) s' (Spec.Sha512.rounds H₀ M₀ (16 * j + 2 * i + 2))
        (Spec.Sha512.rounds H₁ M₁ (16 * j + 2 * i + 2)) ∧ Kept s s' := by
  rw [rounds2, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (kw_ok s i h9 hb hn _ _ _ _ ha hbb) fun s₁ ⟨x0, x1, hx, hg, hm, hrd, hwr⟩ => ?_
  have hv₁ := hv.of_xmm fun r a b => (hx r a b).1
  refine WP.mono (round2_ok (2 * i) w0 (.inl rfl) s₁ _ _ (K (16 * j + 2 * i)) _ _ hv₁ x0) fun s₂ ⟨hv₂, k₂⟩ => ?_
  rw [← round_eq, ← round_eq, ← rounds_succ, ← rounds_succ] at hv₂
  refine WP.mono (round2_ok (2 * i + 1) w1 (.inr rfl) s₂ _ _ (K (16 * j + 2 * i + 1))
    (W M₀ (16 * j + 2 * i + 1)) (W M₁ (16 * j + 2 * i + 1)) hv₂
    (by rw [(k₂.2.2.2.2 w1 (.inr (.inl rfl))).1]; exact x1)) fun s₃ ⟨hv₃, k₃⟩ => ?_
  rw [← round_eq, ← round_eq, ← rounds_succ, ← rounds_succ] at hv₃
  have m1 := hx mB (by decide) (by decide)
  have m2 := k₂.2.2.2.2 mB (.inr (.inr rfl))
  have m3 := k₃.2.2.2.2 mB (.inr (.inr rfl))
  exact ⟨hv₃, k₃.2.2.2.1.trans (k₂.2.2.2.1.trans hg), k₃.1.trans (k₂.1.trans hm),
    k₃.2.1.trans (k₂.2.1.trans hrd), k₃.2.2.1.trans (k₂.2.2.1.trans hwr),
    m3.1.trans (m2.1.trans m1.1), m3.2.trans (m2.2.trans m1.2)⟩

/-! ## The words in the scratch space -/

/-- Where words `t` of both blocks are kept. -/
def wAddr2 (scr : Addr) (t : Nat) : Addr := scr + BitVec.ofNat 64 (16 * t)

/-- Words `t` of both blocks are in the scratch space. -/
def WMem2 (m : Mem) (scr : Addr) (M₀ M₁ : Block) (t : Nat) : Prop :=
  m.readW (wAddr2 scr t) 128 = W M₁ t ++ W M₀ t

theorem wAddr2_succ (scr : Addr) (t : Nat) : wAddr2 scr t + BitVec.ofNat 64 16 = wAddr2 scr (t + 1) := by
  simp only [wAddr2]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 16 * t + 16 = 16 * (t + 1) by omega]

theorem read256_lo (m : Mem) (a : Addr) : (m.readW a 256).extractLsb' 0 128 = m.readW a 128 := by
  have e := readW_extract m a (w := 256) (k := 0) (n := 16) (by decide)
  rw [show a + BitVec.ofNat 64 0 = a from BitVec.add_zero a] at e
  exact e

theorem read256_hi (m : Mem) (a : Addr) :
    (m.readW a 256).extractLsb' 128 128 = m.readW (a + BitVec.ofNat 64 16) 128 :=
  readW_extract m a (w := 256) (k := 16) (n := 16) (by decide)

theorem append_lo (hi lo : BitVec 128) : (hi ++ lo).extractLsb' 0 128 = lo := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi'
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi', decide_true, Bool.true_and, Nat.zero_add,
    ite_true]

theorem append_hi (hi lo : BitVec 128) : (hi ++ lo).extractLsb' 128 128 = hi := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi'
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi', decide_true, Bool.true_and,
    show ¬ 128 + i < 128 by omega, ite_false, show 128 + i - 128 = i by omega]

/-- The two words at `t` and `t + 1`, as one 256-bit load. -/
theorem read256_words {m : Mem} {scr : Addr} {M₀ M₁ : Block} {t : Nat} (h₀ : WMem2 m scr M₀ M₁ t)
    (h₁ : WMem2 m scr M₀ M₁ (t + 1)) :
    (m.readW (wAddr2 scr t) 256).extractLsb' 0 128 = W M₁ t ++ W M₀ t ∧
    (m.readW (wAddr2 scr t) 256).extractLsb' 128 128 = W M₁ (t + 1) ++ W M₀ (t + 1) := by
  rw [read256_lo, read256_hi, wAddr2_succ]; exact ⟨h₀, h₁⟩

theorem wSlot_ea (s : State) {j : Nat} (h9 : s.gpr .r9 = idx2 j) (i : Nat) (d : Int) (t : Nat)
    (ht : ((256 * j + 32 * i : Nat) : Int) + d = ((16 * t : Nat) : Int)) :
    s.ea (wSlot i d) = wAddr2 (s.gpr .r8) t := by
  simp only [State.ea, wSlot, h9, idx2, BitVec.mul_one, wAddr2]
  rw [BitVec.add_assoc, ← ofInt_natCast (256 * j), ← BitVec.ofInt_add, ← ofInt_natCast (16 * t)]
  refine congrArg _ (congrArg _ ?_)
  omega

/-! ## A schedule step -/

/-- What `sched` computes in one lane, from the lane's four loads, as its
instructions do. -/
def sl (a b c d : BitVec 128) : BitVec 128 :=
  XBinOp.eval .paddq (XBinOp.eval .paddq (XBinOp.eval .paddq
    (ternlog (XShiftOp.eval .psrlq a 7) (rorQwords a 1) (rorQwords a 8) 0x96) c) d)
    (ternlog (XShiftOp.eval .psrlq b 6) (rorQwords b 19) (rorQwords b 61) 0x96)

theorem xor3_rot (p q r : Word) : p ^^^ q ^^^ r = q ^^^ r ^^^ p := by
  rw [BitVec.xor_comm p q, BitVec.xor_assoc, BitVec.xor_comm p r, ← BitVec.xor_assoc]

theorem sl_eq (a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ : Word) :
    sl (a₁ ++ a₀) (b₁ ++ b₀) (c₁ ++ c₀) (d₁ ++ d₀) =
      (ssig1 b₁ + d₁ + ssig0 a₁ + c₁) ++ (ssig1 b₀ + d₀ + ssig0 a₀ + c₀) := by
  simp only [sl, ror_eq, tern96_eq, paddq_eq, psrlq_eq _ _ _ (by decide : (7 : BitVec 8).toNat < 64),
    psrlq_eq _ _ _ (by decide : (6 : BitVec 8).toNat < 64), BitVec.reduceToNat, Nat.reduceMod, xor3_rot (_ >>> _)]
  congr 1 <;> (simp only [Spec.Sha512.ssig0, Spec.Sha512.ssig1]; ac_rfl)

/-- `sched`, on the four values it loads. -/
theorem sched_run (i : Nat) (s : State) (pA pB pC pD pO : Addr)
    (eA : s.ea (wSlot i (-240)) = pA) (eB : s.ea (wSlot i (-32)) = pB) (eC : s.ea (wSlot i (-256)) = pC)
    (eD : s.ea (wSlot i (-112)) = pD) (eO : s.ea (wSlot i) = pO)
    (hA : InRegions (s.rd ++ s.wr) pA 32) (hB : InRegions (s.rd ++ s.wr) pB 32)
    (hC : InRegions (s.rd ++ s.wr) pC 32) (hD : InRegions (s.rd ++ s.wr) pD 32) (hO : InRegions s.wr pO 32) :
    WP isa (.block (sched i)) s fun s' =>
      s'.xmm w0 = sl ((s.mem.readW pA 256).extractLsb' 0 128) ((s.mem.readW pB 256).extractLsb' 0 128)
        ((s.mem.readW pC 256).extractLsb' 0 128) ((s.mem.readW pD 256).extractLsb' 0 128) ∧
      s'.ymmHi w0 = sl ((s.mem.readW pA 256).extractLsb' 128 128) ((s.mem.readW pB 256).extractLsb' 128 128)
        ((s.mem.readW pC 256).extractLsb' 128 128) ((s.mem.readW pD 256).extractLsb' 128 128) ∧
      s'.mem = s.mem.writeW pO (s'.ymmHi w0 ++ s'.xmm w0) ∧
      (∀ r, r ≠ w0 → r ≠ w1 → r ≠ u0 → r ≠ u1 → s'.xmm r = s.xmm r ∧ s'.ymmHi r = s.ymmHi r) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  simp only [State.ea, wSlot] at eA eB eC eD eO
  apply WP.of_runBlock
  simp only [sched, vror, vxor3, wSlot, u0, u1, w0, w1, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some,
    runBlock_nil, reduceExec, reduceVOpExec, isa, State.load256, State.store256, State.ea, State.ymm, State.lane,
    RegUpd.xmm_setV, RegUpd.ymmHi_setV_256, RegUpd.gpr_setV, RegUpd.mem_setV, RegUpd.rd_setV, RegUpd.wr_setV,
    eA, eB, eC, eD, eO, hA, hB, hC, hD, hO, Option.map_some, Option.some.injEq, exists_eq_left', reduceVBinOpSse]
  exact ⟨rfl, rfl, trivial, fun r h0 h1 h2 h3 => by simp [h0, h1, h2, h3], trivial, trivial, trivial⟩

/-- The scratch space holds words `t` of both at `wAddr2 scr t`, `32` bytes
from there readable and writable. -/
theorem in_scr2 {s : State} {scr : Addr} (hR : (⟨scr, 1328⟩ : Region) ∈ s.wr) {t : Nat} (ht : t < 79) :
    InRegions s.wr (wAddr2 scr t) 32 ∧ InRegions (s.rd ++ s.wr) (wAddr2 scr t) 32 :=
  ⟨⟨_, hR, contains_offset (by omega) (by omega)⟩,
    ⟨_, List.mem_append_right _ hR, contains_offset (by omega) (by omega)⟩⟩

/-- A stored pair of words: the two words, and the earlier ones kept. -/
theorem wmem2_store {m : Mem} {scr : Addr} {M₀ M₁ : Block} {T : Nat} (hT : T < 79)
    (hm : ∀ t < T, WMem2 m scr M₀ M₁ t) :
    ∀ t < T + 2, WMem2 (m.writeW (wAddr2 scr T) ((W M₁ (T + 1) ++ W M₀ (T + 1)) ++ (W M₁ T ++ W M₀ T)))
      scr M₀ M₁ t := by
  intro t ht
  rcases (by omega : t < T ∨ t = T ∨ t = T + 1) with h | rfl | rfl
  · exact (readW_writeW_off m scr _ (d := 16 * t) (e := 16 * T) (n := 16) (by omega) (by omega)
      (by omega)).trans (hm t h)
  · have e := readW_writeW_inside m (wAddr2 scr t)
      ((W M₁ (t + 1) ++ W M₀ (t + 1)) ++ (W M₁ t ++ W M₀ t)) (k := 0) (n := 16) (by decide) (by decide)
    rw [show wAddr2 scr t + BitVec.ofNat 64 0 = wAddr2 scr t from BitVec.add_zero _] at e
    exact e.trans (append_lo _ _)
  · have e := readW_writeW_inside m (wAddr2 scr T)
      ((W M₁ (T + 1) ++ W M₀ (T + 1)) ++ (W M₁ T ++ W M₀ T)) (k := 16) (n := 16) (by decide) (by decide)
    rw [wAddr2_succ] at e
    exact e.trans (append_hi _ _)

/-- Step `i` of iteration `j ≥ 1` computes words `t` and `t + 1`
(`t = 16 j + 2 i`) of both from the earlier ones, and stores them. -/
theorem sched_ok (s : State) {j : Nat} (i : Nat) (hj : 1 ≤ j) (hn : 8 * j + i < 40) {scr : Addr}
    (M₀ M₁ : Block) (h8 : s.gpr .r8 = scr) (h9 : s.gpr .r9 = idx2 j) (hR : (⟨scr, 1328⟩ : Region) ∈ s.wr)
    (hm : ∀ t < 16 * j + 2 * i, WMem2 s.mem scr M₀ M₁ t) :
    WP isa (.block (sched i)) s fun s' =>
      s'.xmm w0 = W M₁ (16 * j + 2 * i) ++ W M₀ (16 * j + 2 * i) ∧
      s'.ymmHi w0 = W M₁ (16 * j + 2 * i + 1) ++ W M₀ (16 * j + 2 * i + 1) ∧
      (∀ t < 16 * j + 2 * i + 2, WMem2 s'.mem scr M₀ M₁ t) ∧
      Frame [⟨scr, 1280⟩] s.mem s'.mem ∧
      (∀ r, r ≠ w0 → r ≠ w1 → r ≠ u0 → r ≠ u1 → s'.xmm r = s.xmm r ∧ s'.ymmHi r = s.ymmHi r) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨T, hT⟩ : ∃ T, T = 16 * j + 2 * i := ⟨_, rfl⟩
  rw [← hT] at hm ⊢
  have eA := wSlot_ea s h9 i (-240) (T - 15) (by omega)
  have eB := wSlot_ea s h9 i (-32) (T - 2) (by omega)
  have eC := wSlot_ea s h9 i (-256) (T - 16) (by omega)
  have eD := wSlot_ea s h9 i (-112) (T - 7) (by omega)
  have eO := wSlot_ea s h9 i 0 T (by omega)
  rw [h8] at eA eB eC eD eO
  refine WP.mono (sched_run i s _ _ _ _ _ eA eB eC eD eO (in_scr2 hR (by omega)).2 (in_scr2 hR (by omega)).2
    (in_scr2 hR (by omega)).2 (in_scr2 hR (by omega)).2 (in_scr2 hR (by omega)).1)
    fun s' ⟨hx, hy, hmem, hk, hg, hrd, hwr⟩ => ?_
  obtain ⟨a0, a1⟩ := read256_words (hm (T - 15) (by omega)) (by rw [show T - 15 + 1 = T - 14 by omega]; exact hm _ (by omega))
  obtain ⟨b0, b1⟩ := read256_words (hm (T - 2) (by omega)) (by rw [show T - 2 + 1 = T - 1 by omega]; exact hm _ (by omega))
  obtain ⟨c0, c1⟩ := read256_words (hm (T - 16) (by omega)) (by rw [show T - 16 + 1 = T - 15 by omega]; exact hm _ (by omega))
  obtain ⟨d0, d1⟩ := read256_words (hm (T - 7) (by omega)) (by rw [show T - 7 + 1 = T - 6 by omega]; exact hm _ (by omega))
  rw [a0, b0, c0, d0, sl_eq] at hx
  rw [a1, b1, c1, d1, sl_eq] at hy
  simp only [show T - 15 + 1 = T - 14 by omega, show T - 2 + 1 = T - 1 by omega,
    show T - 16 + 1 = T - 15 by omega, show T - 7 + 1 = T - 6 by omega] at hy
  have w0e : W M₁ T ++ W M₀ T = s'.xmm w0 := by
    rw [hx]
    have e := fun M => Proof.Sha512.X86_64.Avx2.W_ge' M (T - 16)
    simp only [show T - 16 + 16 = T by omega, show T - 16 + 14 = T - 2 by omega,
      show T - 16 + 9 = T - 7 by omega, show T - 16 + 1 = T - 15 by omega] at e
    rw [e M₀, e M₁]
  have w1e : W M₁ (T + 1) ++ W M₀ (T + 1) = s'.ymmHi w0 := by
    rw [hy]
    have e := fun M => Proof.Sha512.X86_64.Avx2.W_ge' M (T - 15)
    simp only [show T - 15 + 16 = T + 1 by omega, show T - 15 + 14 = T - 1 by omega,
      show T - 15 + 9 = T - 6 by omega, show T - 15 + 1 = T - 14 by omega] at e
    rw [e M₀, e M₁]
  rw [← w0e, ← w1e] at hmem
  refine ⟨w0e.symm, w1e.symm, ?_, ?_, hk, hg, hrd, hwr⟩
  · rw [hmem]; exact wmem2_store (by omega) hm
  · rw [hmem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_offset (by omega) (by omega))

/-! ## The words of the blocks -/

/-- `vpermq` with `0xD8`: the middle quadwords exchanged, which makes two
words of each block the two blocks' words. -/
theorem permD8 (a b c d : Word) :
    (permQwords ((d ++ c : BitVec 128) ++ (b ++ a : BitVec 128)) 0xD8).extractLsb' 0 128 = c ++ a ∧
    (permQwords ((d ++ c : BitVec 128) ++ (b ++ a : BitVec 128)) 0xD8).extractLsb' 128 128 = d ++ b := by
  have e0 : ((0xD8 : BitVec 8).extractLsb' (2 * 0) 2).toNat = 0 := rfl
  have e1 : ((0xD8 : BitVec 8).extractLsb' (2 * 1) 2).toNat = 2 := rfl
  have e2 : ((0xD8 : BitVec 8).extractLsb' (2 * 2) 2).toNat = 1 := rfl
  have e3 : ((0xD8 : BitVec 8).extractLsb' (2 * 3) 2).toNat = 3 := rfl
  simp only [permQwords, e0, e1, e2, e3, ShaNi.qword256_0, ShaNi.qword256_1, ShaNi.qword256_2,
    ShaNi.qword256_3, ShaNi.lo4, ShaNi.hi4]
  exact ⟨trivial, trivial⟩

/-- Words `2i` and `2i+1` of the two blocks, loaded and stored. -/
theorem load2_ok {i : Nat} (hi : i < 8) (s : State) {p₀ p₁ pO : Addr} {M₀ M₁ : Block}
    (hrsi : s.gpr .rsi = p₀) (hrcx : s.gpr .rcx = p₁) (eO : s.ea (wSlot i) = pO)
    (hin₀ : InRegions (s.rd ++ s.wr) (p₀ + BitVec.ofInt 64 ((16 * i : Nat) : Int)) 16)
    (hin₁ : InRegions (s.rd ++ s.wr) (p₁ + BitVec.ofInt 64 ((16 * i : Nat) : Int)) 16)
    (hout : InRegions s.wr pO 32)
    (hm : s.xmm mB = Impl.Sha512.X86_64.Avx2.bswapMask) (hm' : s.ymmHi mB = Impl.Sha512.X86_64.Avx2.bswapMask)
    (hb₀ : ∀ t : Nat, t < 16 → bswap64 (s.mem.readW (p₀ + BitVec.ofInt 64 ((8 * t : Nat) : Int)) 64) = W M₀ t)
    (hb₁ : ∀ t : Nat, t < 16 → bswap64 (s.mem.readW (p₁ + BitVec.ofInt 64 ((8 * t : Nat) : Int)) 64) = W M₁ t) :
    WP isa (.block (load i)) s fun s' =>
      s'.xmm w0 = W M₁ (2 * i) ++ W M₀ (2 * i) ∧ s'.ymmHi w0 = W M₁ (2 * i + 1) ++ W M₀ (2 * i + 1) ∧
      s'.mem = s.mem.writeW pO ((W M₁ (2 * i + 1) ++ W M₀ (2 * i + 1)) ++ (W M₁ (2 * i) ++ W M₀ (2 * i))) ∧
      (∀ r, r ≠ w0 → r ≠ w1 → s'.xmm r = s.xmm r ∧ s'.ymmHi r = s.ymmHi r) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have q₀ := Proof.Sha512.X86_64.Avx2.load_pair M₀ s.mem p₀ hi hb₀
  have q₁ := Proof.Sha512.X86_64.Avx2.load_pair M₁ s.mem p₁ hi hb₁
  have pd := permD8 (W M₀ (2 * i)) (W M₀ (2 * i + 1)) (W M₁ (2 * i)) (W M₁ (2 * i + 1))
  simp only [Proof.Sha512.X86_64.Avx2.pair] at q₀ q₁
  simp only [State.ea, wSlot] at eO
  simp only [mB] at hm hm'
  apply WP.of_runBlock
  simp only [load, wSlot, w0, w1, mB, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil,
    reduceExec, reduceVOpExec, isa, State.load128, State.store256, State.ea, State.ymm, State.lane,
    Impl.Sha512.X86_64.Avx2.at_, RegUpd.xmm_setV, RegUpd.ymmHi_setV_256, RegUpd.ymmHi_setV_128,
    RegUpd.gpr_setV, RegUpd.mem_setV, RegUpd.rd_setV, RegUpd.wr_setV, hrsi, hrcx, eO, hin₀, hin₁, hout, hm, hm',
    q₀, q₁, pd, Option.map_some, Option.some.injEq, exists_eq_left', reduceVBinOpSse,
    show (1 : BitVec 8).getLsbD 0 = true from rfl]
  exact ⟨trivial, trivial, trivial, fun r h0 h1 => by simp [h0, h1], trivial, trivial, trivial⟩

/-! ## The iterations -/

/-- What a step's first part (`load` or `sched`) leaves for its rounds:
words `T` and `T + 1` of both in `w0` and in the scratch space. -/
def Words (M₀ M₁ : Block) (scr : Addr) (T : Nat) (s s' : State) : Prop :=
  s'.xmm w0 = W M₁ T ++ W M₀ T ∧ s'.ymmHi w0 = W M₁ (T + 1) ++ W M₀ (T + 1) ∧
  (∀ t < T + 2, WMem2 s'.mem scr M₀ M₁ t) ∧ Frame [⟨scr, 1280⟩] s.mem s'.mem ∧
  (∀ r, r ≠ w0 → r ≠ w1 → r ≠ u0 → r ≠ u1 → s'.xmm r = s.xmm r ∧ s'.ymmHi r = s.ymmHi r) ∧
  s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr

/-- After `n` steps of iteration `j`, from the state `sB` the rounds started in. -/
structure SInv (H₀ H₁ : HashValue) (M₀ M₁ : Block) (scr : Addr) (sB : State) (j n : Nat) (s : State) : Prop where
  vars : Vars2 (2 * n) s (Spec.Sha512.rounds H₀ M₀ (16 * j + 2 * n)) (Spec.Sha512.rounds H₁ M₁ (16 * j + 2 * n))
  wmem : ∀ t < 16 * j + 2 * n, WMem2 s.mem scr M₀ M₁ t
  gpr : ∀ r, r ≠ .r9 → s.gpr r = sB.gpr r
  r9 : s.gpr .r9 = idx2 j
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  frame : Frame [⟨scr, 1280⟩] sB.mem s.mem
  mask : s.xmm mB = Impl.Sha512.X86_64.Avx2.bswapMask ∧ s.ymmHi mB = Impl.Sha512.X86_64.Avx2.bswapMask
  syms : s.syms = sB.syms

/-- A step: its words, then its two rounds. -/
theorem step_ok {B : List Instr} {H₀ H₁ : HashValue} {M₀ M₁ : Block} {scr : Addr} {sB : State} {j n : Nat}
    (hax : sB.gpr .rax = sB.syms kSym) (hn : 8 * j + n < 40) {s : State}
    (h : SInv H₀ H₁ M₀ M₁ scr sB j n s)
    (hw : WP isa (.block B) s (Words M₀ M₁ scr (16 * j + 2 * n) s)) :
    WP isa (.block (B ++ rounds2 n)) s (SInv H₀ H₁ M₀ M₁ scr sB j (n + 1)) := by
  rw [WP.block_append_iff]
  refine VG.X86_64.WP.mono_syms hw fun s₁ ⟨x0, x1, hm₁, hf₁, hx₁, hg₁, hrd₁, hwr₁⟩ hsy₁ => ?_
  have hv₁ : Vars2 (2 * n) s₁ (Spec.Sha512.rounds H₀ M₀ (16 * j + 2 * n))
      (Spec.Sha512.rounds H₁ M₁ (16 * j + 2 * n)) := by
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h.vars
    have k := fun q => (hx₁ _ (sv_ne (2 * n) q).1 (sv_ne (2 * n) q).2 (sv_ne' (2 * n) q).1 (sv_ne' (2 * n) q).2).1
    exact ⟨(k 0).trans h0, (k 1).trans h1, (k 2).trans h2, (k 3).trans h3, (k 4).trans h4, (k 5).trans h5,
      (k 6).trans h6, (k 7).trans h7⟩
  have h9₁ : s₁.gpr .r9 = idx2 j := by rw [hg₁]; exact h.r9
  have hax₁ : s₁.gpr .rax = s₁.syms kSym := by
    rw [hg₁, h.gpr _ (by decide), hsy₁, h.syms]; exact hax
  refine VG.X86_64.WP.mono_syms (rounds2_ok s₁ n hn H₀ H₁ M₀ M₁ h9₁ hax₁ hv₁ x0 x1)
    fun s₂ ⟨hv₂, hg₂, hm₂, hrd₂, hwr₂, hk₂, hk₂'⟩ hsy₂ => ?_
  have mk := hx₁ mB (by decide) (by decide) (by decide) (by decide)
  exact {
    vars := by rw [show 2 * (n + 1) = 2 * n + 2 by omega, show 16 * j + (2 * n + 2) = 16 * j + 2 * n + 2 by omega]; exact hv₂
    wmem := fun t ht => by rw [hm₂]; exact hm₁ t (by omega)
    gpr := fun r hr => by rw [hg₂, hg₁]; exact h.gpr r hr
    r9 := by rw [hg₂]; exact h9₁
    rd := hrd₂.trans (hrd₁.trans h.rd)
    wr := hwr₂.trans (hwr₁.trans h.wr)
    frame := by rw [hm₂]; exact h.frame.trans hf₁
    mask := ⟨hk₂.trans (mk.1.trans h.mask.1), hk₂'.trans (mk.2.trans h.mask.2)⟩
    syms := hsy₂.trans (hsy₁.trans h.syms) }

/-- What the code has of the blocks and the scratch space when its rounds
start, in `sB`. -/
structure Base (M₀ M₁ : Block) (p₀ p₁ scr : Addr) (sB : State) : Prop where
  rsi : sB.gpr .rsi = p₀
  rcx : sB.gpr .rcx = p₁
  r8 : sB.gpr .r8 = scr
  rax : sB.gpr .rax = sB.syms kSym
  scrW : (⟨scr, 1328⟩ : Region) ∈ sB.wr
  in₀ : ∀ i < 8, InRegions (sB.rd ++ sB.wr) (p₀ + BitVec.ofInt 64 ((16 * i : Nat) : Int)) 16
  in₁ : ∀ i < 8, InRegions (sB.rd ++ sB.wr) (p₁ + BitVec.ofInt 64 ((16 * i : Nat) : Int)) 16
  blk₀ : ∀ m, Frame [⟨scr, 1280⟩] sB.mem m → ∀ t : Nat, t < 16 →
    bswap64 (m.readW (p₀ + BitVec.ofInt 64 ((8 * t : Nat) : Int)) 64) = W M₀ t
  blk₁ : ∀ m, Frame [⟨scr, 1280⟩] sB.mem m → ∀ t : Nat, t < 16 →
    bswap64 (m.readW (p₁ + BitVec.ofInt 64 ((8 * t : Nat) : Int)) 64) = W M₁ t

/-- The steps of the first iteration, whose words are the blocks'. -/
theorem steps0_ok {H₀ H₁ : HashValue} {M₀ M₁ : Block} {p₀ p₁ scr : Addr} {sB : State}
    (hB : Base M₀ M₁ p₀ p₁ scr sB) {s₀ : State} (h₀ : SInv H₀ H₁ M₀ M₁ scr sB 0 0 s₀) :
    ∀ n ≤ 8, WP isa (steps0 n) s₀ (SInv H₀ H₁ M₀ M₁ scr sB 0 n) := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil h₀
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s h => ?_)
    refine step_ok hB.rax (by omega) h ?_
    have h8 : s.gpr .r8 = scr := (h.gpr _ (by decide)).trans hB.r8
    have hR : (⟨scr, 1328⟩ : Region) ∈ s.wr := h.wr ▸ hB.scrW
    have eO := wSlot_ea s h.r9 n 0 (2 * n) (by omega)
    rw [h8] at eO
    refine WP.mono (load2_ok (by omega) s ((h.gpr _ (by decide)).trans hB.rsi) ((h.gpr _ (by decide)).trans hB.rcx)
      eO (by rw [h.rd, h.wr]; exact hB.in₀ n (by omega)) (by rw [h.rd, h.wr]; exact hB.in₁ n (by omega))
      (in_scr2 hR (by omega)).1 h.mask.1 h.mask.2 (hB.blk₀ _ h.frame) (hB.blk₁ _ h.frame))
      fun s₁ ⟨x0, x1, hm, hx, hg, hrd, hwr⟩ => ?_
    rw [show 16 * 0 + 2 * n = 2 * n by omega]
    refine ⟨x0, x1, ?_, ?_, fun r a b _ _ => hx r a b, hg, hrd, hwr⟩
    · rw [hm]; exact wmem2_store (by omega) (by simpa using h.wmem)
    · rw [hm]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_offset (by omega) (by omega))

/-- The steps of a later iteration, whose words are computed. -/
theorem steps_ok {H₀ H₁ : HashValue} {M₀ M₁ : Block} {p₀ p₁ scr : Addr} {sB : State}
    (hB : Base M₀ M₁ p₀ p₁ scr sB) {j : Nat} (hj : 1 ≤ j) (hj5 : j < 5) {s₀ : State}
    (h₀ : SInv H₀ H₁ M₀ M₁ scr sB j 0 s₀) :
    ∀ n ≤ 8, WP isa (steps n) s₀ (SInv H₀ H₁ M₀ M₁ scr sB j n) := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil h₀
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s h => ?_)
    refine step_ok hB.rax (by omega) h ?_
    exact sched_ok s n hj (by omega) M₀ M₁ ((h.gpr _ (by decide)).trans hB.r8) h.r9 (h.wr ▸ hB.scrW) h.wmem

/-! ## The loop -/

theorem e256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide

theorem stepIdx_ok (s : State) :
    WP isa (.block step) s fun s' =>
      eval .ne s' = some (!(s.gpr .r9 + 256 - BitVec.signExtend 64 (1280 : BitVec 32) == 0)) ∧
      s'.gpr .r9 = s.gpr .r9 + 256 ∧ (∀ r, r ≠ .r9 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi := by
  apply WP.of_runBlock
  simp only [step, ↓reduceIte, Nat.reducePow, and_self, runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc, isa, State.setReg, arithFlags, State.setFlags, e256,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨by simp [eval], trivial, fun r h => by simp [h], trivial⟩

/-- The loop stops after iteration 4: `256 (j + 1) = 1280`. -/
theorem step_idx2 {j : Nat} (hj : j < 5) :
    (idx2 j + 256 - BitVec.signExtend 64 (1280 : BitVec 32) == 0) = (j + 1 == 5) := by
  revert j; decide

theorem idx2_succ (j : Nat) : idx2 j + 256 = idx2 (j + 1) := by
  simp only [idx2]
  rw [show (256 : BitVec 64) = BitVec.ofNat 64 256 from rfl, ← BitVec.ofNat_add]
  congr 1

/-- From an iteration to the next. -/
theorem next_ok {H₀ H₁ : HashValue} {M₀ M₁ : Block} {scr : Addr} {sB : State} {j : Nat} (hj : j < 5)
    {s : State} (h : SInv H₀ H₁ M₀ M₁ scr sB j 8 s) :
    WP isa (.block step) s fun s' =>
      eval .ne s' = some (!(j + 1 == 5)) ∧ SInv H₀ H₁ M₀ M₁ scr sB (j + 1) 0 s' := by
  refine VG.X86_64.WP.mono_syms (stepIdx_ok s) fun s' ⟨he, h9, hg, hm, hrd, hwr, hx, hy⟩ hsy => ?_
  rw [h.r9, step_idx2 hj] at he
  refine ⟨he, ?_⟩
  exact {
    vars := by
      have hv := h.vars
      rw [show 2 * 8 = 16 * 1 + 0 by omega, vars2_add16] at hv
      rw [show 16 * (j + 1) + 2 * 0 = 16 * j + 2 * 8 by omega]
      simp only [Vars2, hx] at hv ⊢
      exact hv
    wmem := fun t ht => by rw [hm]; exact h.wmem t (by omega)
    gpr := fun r hr => (hg r hr).trans (h.gpr r hr)
    r9 := by rw [h9, h.r9, idx2_succ]
    rd := hrd.trans h.rd
    wr := hwr.trans h.wr
    frame := by rw [hm]; exact h.frame
    mask := by rw [hx, hy]; exact h.mask
    syms := hsy.trans h.syms }

/-- The eighty rounds of both. -/
theorem rounds_ok {H₀ H₁ : HashValue} {M₀ M₁ : Block} {p₀ p₁ scr : Addr} {sB : State}
    (hB : Base M₀ M₁ p₀ p₁ scr sB) {s₀ : State} (h₀ : SInv H₀ H₁ M₀ M₁ scr sB 0 0 s₀) :
    WP isa (.seq (steps0 8) (.seq (.block step) (.loop (.seq (steps 8) (.block step)) .ne))) s₀
      (SInv H₀ H₁ M₀ M₁ scr sB 5 0) := by
  refine WP.seq (WP.mono (steps0_ok hB h₀ 8 (Nat.le_refl _)) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (next_ok (by decide) h₁) fun s₂ ⟨_, h₂⟩ => ?_)
  let Inv : Nat → State → Prop := fun m s => ∃ j, m = 5 - j ∧ 1 ≤ j ∧ j < 5 ∧ SInv H₀ H₁ M₀ M₁ scr sB j 0 s
  have hstep : ∀ m s, Inv m s → WP isa (.seq (steps 8) (.block step)) s (fun s' =>
      (eval .ne s' = some false ∧ SInv H₀ H₁ M₀ M₁ scr sB 5 0 s') ∨
      (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
    rintro m s ⟨j, rfl, hj1, hj5, hS⟩
    refine WP.seq (WP.mono (steps_ok hB hj1 hj5 hS 8 (Nat.le_refl _)) fun s₃ h₃ => ?_)
    refine WP.mono (next_ok hj5 h₃) fun s₄ ⟨he, h₄⟩ => ?_
    by_cases hl : j + 1 = 5
    · refine .inl ⟨by rw [he]; simp [hl], ?_⟩
      rw [hl] at h₄; exact h₄
    · exact .inr ⟨by rw [he, show (j + 1 == 5) = false from beq_eq_false_iff_ne.mpr hl]; rfl, 5 - (j + 1), by omega, j + 1, rfl, by omega, by omega, h₄⟩
  exact WP.loop (M := isa) Inv hstep 4 s₂ ⟨1, rfl, Nat.le_refl _, by decide, h₂⟩

end VG.Proof.Sha512.X86_64.Avx512

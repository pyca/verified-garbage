module

public import VerifiedGarbage.Proof.MlDsa.X86.Sign.Inv
import VerifiedGarbage.Proof.MlKem.X86.TopLocal
import VerifiedGarbage.Proof.MlKem.X86.TopSeq
import VerifiedGarbage.Proof.MlKem.X86.TopCall
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlDsa.X86.Sign.Base

/-! ### `MlDsa.X86.Sign.Blocks`, which this module and modules that import it used -/

section

/-!
# ML-DSA signing on x86 (32-bit): the blocks between calls

Loads and stores of words and bytes of `scratch` from `Ctx` (`wp_ldsc`,
`wp_stsc`, `wp_st8sc`), and the pieces made of them: sequences (`seqR_piece`),
the empty block (`nil_piece`), and the branch on `OK` (`okIte_piece`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf ptrTo at_)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece Only wp_cons)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params} {A B : State → State → Prop}

/-- The word of `scratch` at `o`. -/
abbrev scw (s₀ s : State) (o : Nat) : BitVec 32 := s.mem.readW (Buf.addr s₀ (sc o 4)) 32

theorem ea_sc {s₀ s : State} (h : Ctx (Y p) s₀ s) (o : Nat) (n : Nat) :
    s.ea (at_ .esi o) = Buf.addr s₀ (sc o n) := by
  simp only [State.ea, at_]; rw [h.esi]; rfl

/-- `r ← ` the word of `scratch` at `o`. -/
theorem wp_ldsc {s₀ s : State} (hp : TPre (Y p) s₀) (h : Ctx (Y p) s₀ s) {o : Nat} (hc : (Y p).ok (sc o 4) = true)
    {r : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Only [r] s s' → s'.gpr r = scw s₀ s o → WP isa (.block is) s' Q) :
    WP isa (.block (.mov r (.mem (at_ .esi o)) :: is)) s Q := by
  have hin : InRegions (s.rd ++ s.wr) (Buf.addr s₀ (sc o 4)) 4 := by
    have := Buf.inRegR hp hc h.rd h.wr (o := 0) (n := 4) (Nat.le_refl _)
    simpa using this
  exact wp_movm' (by rw [ea_sc h o 4]; exact hin) fun s' o' v' => k s' o' (by rw [v', ea_sc h o 4])

theorem ctx_write {s₀ s : State} (hp : TPre (Y p) s₀) (h : Ctx (Y p) s₀ s) {o n w : Nat} (hc : (Y p).okW (sc o n) = true)
    (hw : w / 8 ≤ n) (v : BitVec w) : Ctx (Y p) s₀ { s with mem := s.mem.writeW (Buf.addr s₀ (sc o n)) v } := by
  obtain ⟨hc₁, hc₂⟩ := Lay.okW_iff.mp hc
  obtain ⟨r, hr, hcr⟩ := Buf.contains hp hc₁ hc₂ (o := 0) (n := w / 8) (by show 0 + w / 8 ≤ n; omega_using [hw])
  rw [BitVec.add_zero] at hcr
  exact ⟨h.esp, h.rd, h.wr, h.esi, h.frame.writeW hr _ hcr⟩

/-- The word of `scratch` at `o` ← `r`. -/
theorem wp_stsc {s₀ s : State} (hp : TPre (Y p) s₀) (h : Ctx (Y p) s₀ s) {o : Nat} (hc : (Y p).okW (sc o 4) = true)
    {r : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Ctx (Y p) s₀ s' → (∀ x, s'.gpr x = s.gpr x) → s'.mem = s.mem.writeW (Buf.addr s₀ (sc o 4)) (s.gpr r) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.store (at_ .esi o) r :: is)) s Q := by
  obtain ⟨hc₁, hc₂⟩ := Lay.okW_iff.mp hc
  have hin : InRegions s.wr (Buf.addr s₀ (sc o 4)) 4 := by
    have := Buf.inRegW hp hc₁ hc₂ h.wr (o := 0) (n := 4) (Nat.le_refl _)
    simpa using this
  refine wp_store' (by rw [ea_sc h o 4]; exact hin) fun s' g' r' w' m' => ?_
  rw [ea_sc h o 4] at m'
  have c := ctx_write hp h hc (w := 32) (by decide) (s.gpr r)
  exact k s' ⟨by rw [g']; exact c.esp, by rw [r']; exact c.rd, by rw [w']; exact c.wr, by rw [g']; exact c.esi,
    by rw [m']; exact c.frame⟩ g' m'

/-- The byte of `scratch` at `o` ← the low byte of `r`. -/
theorem wp_st8sc {s₀ s : State} (hp : TPre (Y p) s₀) (h : Ctx (Y p) s₀ s) {o : Nat} (hc : (Y p).okW (sc o 1) = true)
    {r : Reg8} {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Ctx (Y p) s₀ s' → (∀ x, s'.gpr x = s.gpr x) →
      s'.mem = s.mem.writeW (Buf.addr s₀ (sc o 1)) ((s.gpr r.reg).setWidth 8) → WP isa (.block is) s' Q) :
    WP isa (.block (.store8 (at_ .esi o) r :: is)) s Q := by
  obtain ⟨hc₁, hc₂⟩ := Lay.okW_iff.mp hc
  have hin : InRegions s.wr (Buf.addr s₀ (sc o 1)) 1 := by
    have := Buf.inRegW hp hc₁ hc₂ h.wr (o := 0) (n := 1) (Nat.le_refl _)
    simpa using this
  refine wp_store8 (by rw [ea_sc h o 1]; exact hin) ?_
  rw [ea_sc h o 1]
  exact k _ (ctx_write hp h hc (w := 8) (by decide) _) (fun _ => rfl) rfl

theorem wp_addr {d r : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr d + s.gpr r → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.reg r) :: is)) s Q :=
  wp_cons (s' := (arithFlags s (s.gpr d + s.gpr r) (decide (2 ^ 32 ≤ (s.gpr d).toNat + (s.gpr r).toNat))
      (addOverflow (s.gpr d) (s.gpr r) (s.gpr d + s.gpr r))).setReg d (s.gpr d + s.gpr r))
    (by simp only [exec, execAlu, readSrc, Option.bind_some])
    (k _ (Only.flags s d _ _ _) (by simp [State.setReg]))

theorem wp_test {r : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [] s s' → s'.zf = some (s.gpr r &&& s.gpr r == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .test r (.reg r) :: is)) s Q :=
  wp_cons (s' := arithFlags s (s.gpr r &&& s.gpr r) false false)
    (by simp only [exec, execAlu, readSrc, Option.bind_some])
    (k _ ⟨fun _ _ => rfl, rfl, rfl, rfl⟩ rfl)

theorem wp_subi {d : Reg} {v : BitVec 32} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr d - v → s'.zf = some (s.gpr d - v == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.imm v) :: is)) s Q :=
  wp_cons (s' := (arithFlags s (s.gpr d - v) (decide ((s.gpr d).toNat < v.toNat))
      (subOverflow (s.gpr d) v (s.gpr d - v))).setReg d (s.gpr d - v))
    (by simp only [exec, execAlu, readSrc, Option.bind_some])
    (k _ (Only.flags s d _ _ _) (by simp [State.setReg]) rfl)

/-! ## Pieces -/

/-- The empty block. -/
theorem nil_piece (h : ∀ s₀ s, TPre (Y p) s₀ → A s₀ s → B s₀ s) : SP p A B (.block []) where
  wp s₀ s hp ha := WP.block_nil_iff.mpr (h s₀ s hp ha)
  ct _ _ _ _ _ := fun _ _ _ _ _ _ _ e₁ e₂ => by
    rw [Exec.block_iff] at e₁ e₂
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
    exact ⟨e₁.2.symm.trans e₂.2, trivial⟩

/-- `f a, …, f (a + n - 1)`, from pieces for each. -/
theorem seqR_piece {f : Nat → Prog isa} {I : Nat → State → State → Prop} :
    ∀ (a n : Nat), (∀ i, a ≤ i → i < a + n → SP p (I i) (I (i + 1)) (f i)) → SP p (I a) (I (a + n)) (seqR f a n)
  | a, 0, _ => nil_piece fun _ _ _ h => h
  | a, n + 1, h => by
    refine Piece.seq (h a (Nat.le_refl _) (by omega_using [])) ?_
    have := seqR_piece (I := I) (a + 1) n fun i hi hi' => h i (by omega_using [hi]) (by omega_using [hi'])
    rwa [show a + 1 + n = a + (n + 1) by omega_using []] at this

/-- The branch on `OK`, which is 1 or 0 as `b` of the initial state says. -/
theorem okIte_piece (hc : (Y p).ok (sc oOK 4) = true) {t e : Prog isa} (b : State → Bool)
    (hA : ∀ s₀ s, TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s ∧ scw s₀ s oOK = if b s₀ then 1 else 0)
    (hb : ∀ s₀ s₀', TPre (Y p) s₀ → TPre (Y p) s₀' → SPub p s₀ s₀' → b s₀ = b s₀')
    (ht : SP p (fun s₀ s₁ => (∃ s, A s₀ s ∧ Ctx (Y p) s₀ s₁ ∧ s₁.mem = s.mem) ∧ b s₀ = true) B t)
    (he : SP p (fun s₀ s₁ => (∃ s, A s₀ s ∧ Ctx (Y p) s₀ s₁ ∧ s₁.mem = s.mem) ∧ b s₀ = false) B e) :
    SP p A B (ifOkElse t e) := by
  refine Piece.seq (B := fun s₀ s₁ => (∃ s, A s₀ s ∧ Ctx (Y p) s₀ s₁ ∧ s₁.mem = s.mem) ∧
    s₁.zf = some (!b s₀)) (blk_piece (fun s₀ s hp ha => (hA s₀ s hp ha).1) (fun s₀ s hp ha => ?_) rfl) ?_
  · obtain ⟨h, hok⟩ := hA s₀ s hp ha
    refine wp_ldsc hp h hc fun s₁ o₁ v₁ => wp_test fun s₂ o₂ z₂ => WP.block_nil_iff.mpr ?_
    have o := o₁.trans o₂
    refine ⟨⟨s, ha, h.only o (by simp) (by simp), o.mem⟩, ?_⟩
    rw [z₂, v₁, hok]
    cases b s₀ <;> rfl
  · refine Piece.ite b (fun s₀ s₁ hp ha => ?_) hb (ht.mono (fun _ _ _ h => ⟨h.1.1, h.2⟩) fun _ _ _ h => h)
      (he.mono (fun _ _ _ h => ⟨h.1.1, h.2⟩) fun _ _ _ h => h)
    show s₁.zf.map (!·) = _
    rw [ha.2]; cases b s₀ <;> rfl

end VG.Proof.MlDsa.X86.Sign

end

end

/-!
# ML-DSA signing on x86 (32-bit): words and bytes of `scratch`

The small blocks between calls, as what they leave in `scratch` and the frame
of what they change: a word or a byte set (`wp_st32`, `wp_st8`), `OK ← OK ∧
eax` (`wp_andOK`) and `ONES ← ONES + eax` (`wp_addOnes`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf at_)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Only wp_cons)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params}

theorem sc_ok (ps : PS p) {o n : Nat} (h : o + n ≤ 5120) (hn : 0 < n) : (Y p).okW (sc o n) = true := by ofs

theorem sc_ok' (ps : PS p) {o n : Nat} (h : o + n ≤ 5120) (hn : 0 < n) : (Y p).ok (sc o n) = true :=
  (Lay.okW_iff.mp (sc_ok ps h hn)).1

/-- The address of a part of a buffer. -/
theorem addr_off {Y : Lay} {s₀ : State} (hp : TPre Y s₀) {a o d l l' : Nat} (h₁ : Y.ok ⟨a, o, l⟩ = true)
    (h₂ : Y.ok ⟨a, o + d, l'⟩ = true) : Buf.addr s₀ ⟨a, o + d, l'⟩ = Buf.addr s₀ ⟨a, o, l⟩ + BitVec.ofNat 64 d := by
  rw [Buf.addr_eq hp h₂, Buf.addr_eq hp h₁, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem bytes1_write (m : Mem) (a : Addr) (v : Byte) : bytesAt (m.writeW a v) a 1 = [v] := by
  simp only [bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero,
    VG.Proof.MlKem.writeW8_apply, ite_true]

theorem setWidth8_ofNat (v : Nat) : (BitVec.ofNat 32 v).setWidth 8 = BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd v (by decide)

theorem and01 (a b : Bool) :
    ((if a then 1 else 0 : BitVec 32) &&& (if b then 1 else 0)) = if a && b then 1 else 0 := by
  cases a <;> cases b <;> rfl

section
variable {s₀ s : State} (hp : TPre (Y p) s₀) (h : Ctx (Y p) s₀ s)
include hp h

/-- The word at `o` set to `v`. -/
theorem wp_st32 {o : Nat} (hc : (Y p).okW (sc o 4) = true) (v : Nat) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Ctx (Y p) s₀ s' → Frame (FR s₀ [sc o 4] 0) s.mem s'.mem → scw s₀ s' o = BitVec.ofNat 32 v →
      WP isa (.block is) s' Q) :
    WP isa (.block (st32 o v ++ is)) s Q := by
  simp only [st32, List.cons_append, List.nil_append]
  refine wp_movi fun s₁ o₁ v₁ => ?_
  refine wp_stsc hp (h.only o₁ (by simp) (by simp)) hc fun s₂ c₂ g₂ m₂ => k s₂ c₂ ?_ ?_
  · rw [m₂, o₁.mem]; exact frW32 (Y := Y p)
  · rw [scw, m₂, Mem.readW_writeW_self32, v₁]

/-- The byte at `o` set to `v`. -/
theorem wp_st8 {o : Nat} (hc : (Y p).okW (sc o 1) = true) (v : Nat) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Ctx (Y p) s₀ s' → Frame (FR s₀ [sc o 1] 0) s.mem s'.mem →
      bytesAt s'.mem (Buf.addr s₀ (sc o 1)) 1 = [BitVec.ofNat 8 v] → WP isa (.block is) s' Q) :
    WP isa (.block (st8 o v ++ is)) s Q := by
  simp only [st8, List.cons_append, List.nil_append]
  refine wp_movi fun s₁ o₁ v₁ => ?_
  refine wp_st8sc hp (h.only o₁ (by simp) (by simp)) hc fun s₂ c₂ g₂ m₂ => k s₂ c₂ ?_ ?_
  · rw [m₂, o₁.mem]; exact frW8 (Y := Y p)
  · rw [m₂, bytes1_write]; show [(s₁.gpr .eax).setWidth 8] = _; rw [v₁, setWidth8_ofNat]

/-- `OK ← OK ∧ eax`. -/
theorem wp_andOK (ps : PS p) {Q : State → Prop}
    (k : ∀ s', Ctx (Y p) s₀ s' → Frame (FR s₀ [sc oOK 4] 0) s.mem s'.mem →
      scw s₀ s' oOK = scw s₀ s oOK &&& s.gpr .eax → Q s') :
    WP isa (.block andOK) s Q := by
  unfold andOK
  refine wp_ldsc hp h (sc_ok' ps (by decide) (by decide)) fun s₁ o₁ v₁ => wp_andr fun s₂ o₂ v₂ => ?_
  have o := o₁.trans o₂
  refine wp_stsc hp (h.only o (by simp) (by simp)) (sc_ok ps (by decide) (by decide)) fun s₃ c₃ g₃ m₃ =>
    WP.block_nil_iff.mpr (k s₃ c₃ ?_ ?_)
  · rw [m₃, o.mem]; exact frW32 (Y := Y p)
  · rw [scw, m₃, Mem.readW_writeW_self32, v₂, v₁, o₁.gpr .eax (by simp)]

/-- `ONES ← ONES + eax`. -/
theorem wp_addOnes (ps : PS p) {Q : State → Prop}
    (k : ∀ s', Ctx (Y p) s₀ s' → Frame (FR s₀ [sc oONES 4] 0) s.mem s'.mem →
      scw s₀ s' oONES = scw s₀ s oONES + s.gpr .eax → Q s') :
    WP isa (.block addOnes) s Q := by
  unfold addOnes
  refine wp_ldsc hp h (sc_ok' ps (by decide) (by decide)) fun s₁ o₁ v₁ => wp_addr fun s₂ o₂ v₂ => ?_
  have o := o₁.trans o₂
  refine wp_stsc hp (h.only o (by simp) (by simp)) (sc_ok ps (by decide) (by decide)) fun s₃ c₃ g₃ m₃ =>
    WP.block_nil_iff.mpr (k s₃ c₃ ?_ ?_)
  · rw [m₃, o.mem]; exact frW32 (Y := Y p)
  · rw [scw, m₃, Mem.readW_writeW_self32, v₂, v₁, o₁.gpr .eax (by simp)]

end

/-! ## Frames of the small blocks -/

theorem fr0 {s₀ : State} (hp : TPre (Y p) s₀) {bs : List Buf} {N : Nat} (hN : N ≤ 80) {m m' : Mem}
    (fr : Frame (FR s₀ bs 0) m m') : Frame (FR s₀ bs N) m m' :=
  fr.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
        stk_sub hp (Nat.zero_le N) (by show N + 16 ≤ 96; omega_using [hN])⟩

theorem scr_ge (ps : PS p) : oP (nS p) ≤ scrLen p := by ofsd

/-- The frame of a piece that writes only in `scratch[lo : hi]`, as that buffer. -/
theorem frSc {s₀ : State} (hp : TPre (Y p) s₀) {bs : List Buf} {N M : Nat} (hNM : N ≤ M) (hM : M ≤ 80)
    {lo hi : Nat} (hlh : lo < hi) (hhi : hi ≤ scrLen p)
    (h : ∀ c ∈ bs, c.arg = SC ∧ lo ≤ c.off ∧ c.off + c.len ≤ hi ∧ 0 < c.len) {m m' : Mem}
    (fr : Frame (FR s₀ bs N) m m') : Frame (FR s₀ [sc lo (hi - lo)] M) m m' :=
  frIn hp hNM hM (fun c hc => by
    obtain ⟨h₁, h₂, h₃, h₄⟩ := h c hc
    refine ⟨Lay.ok_iff.mpr ⟨by rw [h₁, Y_n]; decide, h₄, by rw [h₁, Y_alen4]; omega_using [hhi, h₃]⟩, _, List.mem_singleton_self _,
      Lay.ok_iff.mpr ⟨by rw [Y_n]; exact (by decide : 4 < 5), by simp only; omega_using [hlh], by rw [Y_alen4]; simp only; omega_using [hlh, hhi]⟩, h₁, by simp only; omega_using [h₂],
      by simp only; omega_using [h₃]⟩) fr

/-- `keepB`, for bytes of `scratch` that may be none. -/
theorem keepB0 {s₀ : State} (hp : TPre (Y p) s₀) {bs : List Buf} {N : Nat} (hN : N ≤ 80)
    {m m' : Mem} (fr : Frame (FR s₀ bs N) m m') {o l : Nat} (L : Nat) (hl : o + l ≤ scrLen p)
    (h : ∀ c ∈ bs, Out p o (o + l) c) : bytesAt m' (Buf.addr s₀ (sc o L)) l = bytesAt m (Buf.addr s₀ (sc o L)) l := by
  rcases Nat.eq_zero_or_pos l with rfl | hl0
  · rfl
  · exact keepB hp hN fr (l := l) (Lay.ok_iff.mpr ⟨by rw [Y_n]; exact (by decide : 4 < 5), hl0, by rw [Y_alen4]; exact hl⟩) h

end VG.Proof.MlDsa.X86.Sign

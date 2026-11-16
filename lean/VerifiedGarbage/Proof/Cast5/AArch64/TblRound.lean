module

public import VerifiedGarbage.Proof.Cast5.AArch64.TblSbox
public import VerifiedGarbage.Proof.Blowfish.AArch64.Round
public import VerifiedGarbage.Proof.Cast5.AArch64.Block
import VerifiedGarbage.Proof.Cast5.Rotate
import VerifiedGarbage.Proof.Blowfish.AArch64.Lanes
import VerifiedGarbage.Proof.Blowfish.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint

/-!
# CAST5 on AArch64: one round on sixteen blocks

`round_ok`: `round t up`, with `x5` at `Kmᵢ` in the subkeys, for a round `i`
of Type `t`, leaves `R` in `A` and `L ^ f(R, Kmᵢ, Krᵢ)` in `B`, word by
word, and moves `x5` to the next subkey (`up`) or the previous one.
-/

@[expose] public section

namespace VG.Proof.Cast5.AArch64.Tbl

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Cast5.AArch64.Tbl
open VG.Impl.Blowfish.AArch64 (aReg bReg fReg idxReg outReg qReg tReg c64 c128 veor vperm planeOff
  planes words wordReg)
open VG.AArch64.Tbl (VOnly)
open VG.Spec.Cast5 (Word)

/-! ## Words -/

def opEval (o : Op) (a b : Word) : Word :=
  match o with
  | .add => a + b
  | .eor => a ^^^ b
  | .sub => a - b

/-- `f`'s accumulation through S-box `j`, for a round of Type `t` on `I = i`. -/
def fAcc (t : Nat) (i : Word) : Nat → Word
  | 0 => sbox 0 (Spec.Cast5.byte i 0)
  | j + 1 => opEval (op t (j + 1)) (fAcc t i j) (sbox (j + 1) (Spec.Cast5.byte i (j + 1)))

/-- §2.2's `f` of round `i`, of Type `t`. -/
theorem f_eq_fAcc {t i : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) (hi : i % 3 = t % 3) (d km kr : Word) :
    Spec.Cast5.f i d km kr = fAcc t ((opEval (op t 0) km d).rotateLeft (kr.toNat % 32)) 3 := by
  rcases ht with rfl | rfl | rfl
  · have : i % 3 = 1 := hi
    simp only [Spec.Cast5.f, this, fAcc, op, opEval, sbox]
  · have : i % 3 = 2 := hi
    simp only [Spec.Cast5.f, this, fAcc, op, opEval, sbox]
  · have : i % 3 = 0 := hi
    simp only [Spec.Cast5.f, this, fAcc, op, opEval, sbox]

theorem byte_eq (i : Word) (j : Nat) : Spec.Cast5.byte i j = i.extractLsb' (8 * (3 - j)) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [Spec.Cast5.byte, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb', hk,
    decide_true, Bool.true_and]

/-- The rotation, as the halves of a 64-bit product by a power of two. -/
theorem one_rot : ∀ r < 32, ((1 : Word).rotateLeft r).setWidth 64 = BitVec.twoPow 64 r := by decide
theorem rot_mul (x : Word) {r : Nat} (hr : r < 32) :
    (x.setWidth 64 * ((1 : Word).rotateLeft r).setWidth 64).extractLsb' 0 32 |||
      (x.setWidth 64 * ((1 : Word).rotateLeft r).setWidth 64).extractLsb' 32 32 = x.rotateLeft r := by
  rw [one_rot r hr, BitVec.mul_twoPow_eq_shiftLeft]
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [Proof.Cast5.getLsbD_rotateLeft_lt _ hr hk, BitVec.getLsbD_or, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_setWidth]
  have h2 : 32 + k < 64 := by omega
  simp only [hk, h2, decide_true, Bool.true_and, Nat.zero_add]
  by_cases hkr : k < r
  · have e : 32 + k - r = 32 - r + k := by omega
    have h3 : ¬ 32 + k < r := by omega
    have h4 : 32 - r + k < 64 := by omega
    simp [show k < 64 by omega, hkr, h3, e, h4]
  · have h3 : ¬ 32 + k < r := by omega
    have h5 : k - r < 64 := by omega
    have h6 : x.getLsbD (32 + k - r) = false := BitVec.getLsbD_of_ge _ _ (by omega)
    simp [show k < 64 by omega, hkr, h3, h5, h6]
theorem vword_ofVDwords (a b : BitVec 64) {k : Nat} (hk : k < 4) :
    vword (ofVDwords a b) k = (if k < 2 then a else b).extractLsb' (32 * (k % 2)) 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
    simp only [vword, ofVDwords, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and] <;>
    simp <;> (try split) <;> first | omega | rfl | (congr 1; omega)

theorem vword_or (x y : BitVec 128) (e : Nat) : vword (x ||| y) e = vword x e ||| vword y e := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [vword, hi]

/-! ## What a step keeps -/

/-- Only the general-purpose registers `gs` and the vector registers `vs`
(and the flags) change. -/
structure RFrame (gs : List Reg) (vs : List VReg) (s s' : State) : Prop where
  g : ∀ r, r ∉ gs → s'.gpr r = s.gpr r
  v : ∀ r, r ∉ vs → s'.v r = s.v r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  syms : s'.syms = s.syms

theorem RFrame.trans {gs : List Reg} {vs : List VReg} {a b c : State} (h₁ : RFrame gs vs a b)
    (h₂ : RFrame gs vs b c) : RFrame gs vs a c :=
  ⟨fun r hr => (h₂.g r hr).trans (h₁.g r hr), fun r hr => (h₂.v r hr).trans (h₁.v r hr),
    h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp, h₂.syms.trans h₁.syms⟩

theorem RFrame.mono {gs gs' : List Reg} {vs vs' : List VReg} {a b : State} (h : RFrame gs vs a b)
    (hg : ∀ r ∈ gs, r ∈ gs') (hv : ∀ r ∈ vs, r ∈ vs') : RFrame gs' vs' a b :=
  ⟨fun r hr => h.g r fun h' => hr (hg r h'), fun r hr => h.v r fun h' => hr (hv r h'), h.mem, h.rd, h.wr,
    h.sp, h.syms⟩

theorem RFrame.ofV {vs : List VReg} {a b : State} (h : VOnly vs a b) : RFrame [] vs a b := by
  refine ⟨fun r _ => ?_, h.2, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [h.1]

theorem vmono {ds ds' : List VReg} {a b : State} (h : VOnly ds a b) (hs : ∀ r ∈ ds, r ∈ ds') :
    VOnly ds' a b := Proof.Blowfish.AArch64.VOnly.mono h hs

/-! ## Four registers, one instruction each -/

/-- Four instructions, instruction `k` writing `D k` with a value `g k` that
reads, of the registers `D`, at most `D k`. -/
theorem map4_run (s : State) (ins : Nat → Instr) (D : Nat → VReg)
    (g : Nat → (VReg → BitVec 128) → BitVec 128)
    (he : ∀ k < 4, ∀ u : State, exec (ins k) u = some (u.setV (D k) (g k u.v)))
    (hinj : ∀ k < 4, ∀ k' < 4, k ≠ k' → D k ≠ D k')
    (hg : ∀ k < 4, ∀ v v' : VReg → BitVec 128, (∀ r, (∀ k' < 4, k' ≠ k → r ≠ D k') → v' r = v r) →
      g k v' = g k v) :
    ∃ s', runBlock isa ((List.range 4).map ins) s = some s' ∧ (∀ k < 4, s'.v (D k) = g k s.v) ∧
      VOnly [D 0, D 1, D 2, D 3] s s' := by
  let s₁ := s.setV (D 0) (g 0 s.v)
  let s₂ := s₁.setV (D 1) (g 1 s₁.v)
  let s₃ := s₂.setV (D 2) (g 2 s₂.v)
  let s₄ := s₃.setV (D 3) (g 3 s₃.v)
  have hl : (List.range 4).map ins = [ins 0, ins 1, ins 2, ins 3] := rfl
  have ne := fun k hk k' hk' (h : k ≠ k') => hinj k hk k' hk' h
  refine ⟨s₄, ?_, ?_, ?_⟩
  · rw [hl, runBlock_cons, he 0 (by decide), runStep_some, runBlock_cons, he 1 (by decide), runStep_some,
      runBlock_cons, he 2 (by decide), runStep_some, runBlock_cons, he 3 (by decide), runStep_some,
      runBlock_nil]
  · intro k hk
    rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · show (s₃.setV _ _).v _ = _
      rw [v_setV_of_ne _ _ (ne 0 (by decide) 3 (by decide) (by decide))]
      show (s₂.setV _ _).v _ = _
      rw [v_setV_of_ne _ _ (ne 0 (by decide) 2 (by decide) (by decide))]
      show (s₁.setV _ _).v _ = _
      rw [v_setV_of_ne _ _ (ne 0 (by decide) 1 (by decide) (by decide))]
      exact v_setV_self _ _ _
    · show (s₃.setV _ _).v _ = _
      rw [v_setV_of_ne _ _ (ne 1 (by decide) 3 (by decide) (by decide))]
      show (s₂.setV _ _).v _ = _
      rw [v_setV_of_ne _ _ (ne 1 (by decide) 2 (by decide) (by decide))]
      show (s₁.setV _ _).v _ = _
      rw [v_setV_self]
      exact hg 1 (by decide) _ _ fun r hr => v_setV_of_ne _ _ (hr 0 (by decide) (by decide))
    · show (s₃.setV _ _).v _ = _
      rw [v_setV_of_ne _ _ (ne 2 (by decide) 3 (by decide) (by decide))]
      show (s₂.setV _ _).v _ = _
      rw [v_setV_self]
      exact hg 2 (by decide) _ _ fun r hr =>
        (v_setV_of_ne _ _ (hr 1 (by decide) (by decide))).trans (v_setV_of_ne _ _ (hr 0 (by decide) (by decide)))
    · show (s₃.setV _ _).v _ = _
      rw [v_setV_self]
      exact hg 3 (by decide) _ _ fun r hr =>
        (v_setV_of_ne _ _ (hr 2 (by decide) (by decide))).trans
          ((v_setV_of_ne _ _ (hr 1 (by decide) (by decide))).trans (v_setV_of_ne _ _ (hr 0 (by decide) (by decide))))
  · exact (((VOnly.setV s (by simp) _).trans (VOnly.setV _ (by simp) _)).trans
      (VOnly.setV _ (by simp) _)).trans (VOnly.setV _ (by simp) _)

/-! ## The operations -/

/-- An operation on the four words of two vectors. -/
def opV (o : Op) (x y : BitVec 128) : BitVec 128 :=
  match o with
  | .add => VArr.s4.map2 (fun _ a b => a + b) x y
  | .eor => x ^^^ y
  | .sub => VArr.s4.map2 (fun _ a b => a - b) x y

theorem exec_op (o : Op) (s : State) (d n m : VReg) :
    exec (o.instr d n m) s = some (s.setV d (opV o (s.v n) (s.v m))) := by
  cases o
  · exact (rfl : exec (.vop (.add .s4 d n m)) s = _)
  · exact (rfl : exec (veor d n m) s = _)
  · exact (rfl : exec (.vop (.sub .s4 d n m)) s = _)

theorem vword_opV (o : Op) (x y : BitVec 128) {l : Nat} (hl : l < 4) :
    vword (opV o x y) l = opEval o (vword x l) (vword y l) := by
  cases o
  · show vword (VArr.s4.map2 (fun _ a b => a + b) x y) l = vword x l + vword y l
    rw [vword_map2 _ x y hl]
  · exact Proof.Blowfish.AArch64.vword_xor x y l
  · show vword (VArr.s4.map2 (fun _ a b => a - b) x y) l = vword x l - vword y l
    rw [vword_map2 _ x y hl]

/-! ## `f` -/

open VG.Proof.Blowfish.AArch64 (lane planes_run words_run word_ext vbyte_word lookupRegs wordsRegs fRegs
  stepRegs planesRegs halfRegs Consts fReg_notin idx_notin_step const_notin_step wordReg_ne_fReg fReg_ne)

/-- What `combine t j` does to a register of `f` and a register of words. -/
def cop (t j : Nat) (x y : BitVec 128) : BitVec 128 := if j = 0 then y else opV (op t j) x y

theorem vword_cop (t j : Nat) (x y : BitVec 128) {l : Nat} (hl : l < 4) :
    vword (cop t j x y) l = if j = 0 then vword y l else opEval (op t j) (vword x l) (vword y l) := by
  simp only [cop]
  split
  · rfl
  · exact vword_opV _ x y hl

theorem combine_run (s : State) (t j : Nat) :
    ∃ s', runBlock isa (combine t j) s = some s' ∧
      (∀ k < 4, s'.v (fReg k) = cop t j (s.v (fReg k)) (s.v (wordReg k))) ∧ VOnly fRegs s s' := by
  refine map4_run s (fun k => if j = 0 then .vop (.mov (fReg k) (wordReg k))
      else (op t j).instr (fReg k) (fReg k) (wordReg k)) fReg
    (fun k v => cop t j (v (fReg k)) (v (wordReg k))) (fun k _ u => ?_) fReg_ne (fun k hk v v' h => ?_)
  · simp only [cop]
    split
    · rfl
    · exact exec_op _ _ _ _ _
  · show cop t j (v' (fReg k)) (v' (wordReg k)) = cop t j (v (fReg k)) (v (wordReg k))
    rw [h (fReg k) fun k' hk' hne => fReg_ne k hk k' hk' (Ne.symm hne),
      h (wordReg k) fun k' hk' _ => wordReg_ne_fReg k hk k' hk']

theorem sbox_run {s : State} (h9 : s.gpr .x9 = s.syms planesSym) (hc : Consts s) {j : Nat} (hj : j < 4)
    (t : Nat) (x : Nat → Word) (hx : ∀ n < 16, vbyte (s.v (idxReg j)) n = Spec.Cast5.byte (x n) j)
    (hprev : 0 < j → ∀ n < 16, lane s.v fReg n = fAcc t (x n) (j - 1)) :
    ∃ s', runBlock isa (lookup j ++ words ++ combine t j) s = some s' ∧
      (∀ n < 16, lane s'.v fReg n = fAcc t (x n) j) ∧ VOnly stepRegs s s' := by
  obtain ⟨s₁, r₁, v₁, o₁⟩ := lookup_run h9 hc hj
  obtain ⟨s₂, r₂, v₂, o₂⟩ := words_run s₁
  obtain ⟨s₃, r₃, v₃, o₃⟩ := combine_run s₂ t j
  refine ⟨s₃, VG.AArch64.Tbl.runBlock_cat_some (VG.AArch64.Tbl.runBlock_cat_some r₁ r₂) r₃, ?_, ?_⟩
  · intro n hn
    have hk : n / 4 < 4 := by omega_using [hn]
    have hl : n % 4 < 4 := by omega_using []
    have w : vword (s₂.v (wordReg (n / 4))) (n % 4) = sbox j (Spec.Cast5.byte (x n) j) := by
      refine word_ext fun b hb => ?_
      rw [← vbyte_word _ hb, v₂ _ hk _ hl _ hb, show 4 * (n / 4) + n % 4 = n by omega_using [], v₁ _ hb _ hn, hx n hn]
    have f₂ : s₂.v (fReg (n / 4)) = s.v (fReg (n / 4)) := by
      rw [o₂.2 _ (fReg_notin _ hk).2, o₁.2 _ (fReg_notin _ hk).1]
    simp only [lane]
    rw [v₃ _ hk, vword_cop _ _ _ _ hl, w, f₂]
    rcases j with _ | j'
    · rfl
    · have hp := hprev (Nat.succ_pos _) n hn
      simp only [lane, Nat.add_sub_cancel] at hp
      rw [ite_eq_right (Nat.succ_ne_zero _), hp]
      rfl
  · exact ((Proof.Blowfish.AArch64.VOnly.mono o₁ (by decide)).trans (Proof.Blowfish.AArch64.VOnly.mono o₂ (by decide))).trans
      (Proof.Blowfish.AArch64.VOnly.mono o₃ (by decide))

theorem f_eq (t : Nat) :
    f t = (lookup 0 ++ words ++ combine t 0) ++ ((lookup 1 ++ words ++ combine t 1) ++
      ((lookup 2 ++ words ++ combine t 2) ++ ((lookup 3 ++ words ++ combine t 3) ++ []))) := rfl

/-- `f`'s S-boxes and operations, of sixteen words whose byte planes are in `idxReg`. -/
theorem f_run {s : State} (h9 : s.gpr .x9 = s.syms planesSym) (hc : Consts s) (t : Nat) (x : Nat → Word)
    (hx : ∀ j < 4, ∀ n < 16, vbyte (s.v (idxReg j)) n = Spec.Cast5.byte (x n) j) :
    ∃ s', runBlock isa (f t) s = some s' ∧ (∀ n < 16, lane s'.v fReg n = fAcc t (x n) 3) ∧
      VOnly stepRegs s s' := by
  have keep : ∀ {u : State}, VOnly stepRegs s u →
      u.gpr .x9 = u.syms planesSym ∧ Consts u ∧
        (∀ j < 4, ∀ n < 16, vbyte (u.v (idxReg j)) n = Spec.Cast5.byte (x n) j) := by
    intro u hu
    refine ⟨by rw [hu.gpr, hu.1]; exact h9, ⟨fun e he => ?_, fun e he => ?_⟩, fun j hj n hn => ?_⟩
    · rw [hu.2 _ const_notin_step.1]; exact hc.1 e he
    · rw [hu.2 _ const_notin_step.2]; exact hc.2 e he
    · rw [hu.2 _ (idx_notin_step j hj)]; exact hx j hj n hn
  obtain ⟨s₀, r₀, v₀, o₀⟩ := sbox_run h9 hc (by decide : 0 < 4) t x (hx 0 (by decide)) (by intro h; omega)
  have k₀ := keep o₀
  obtain ⟨s₁, r₁, v₁, o₁⟩ := sbox_run k₀.1 k₀.2.1 (by decide : 1 < 4) t x (k₀.2.2 1 (by decide))
    (fun _ n hn => v₀ n hn)
  have p₁ := o₀.trans o₁
  have k₁ := keep p₁
  obtain ⟨s₂, r₂, v₂, o₂⟩ := sbox_run k₁.1 k₁.2.1 (by decide : 2 < 4) t x (k₁.2.2 2 (by decide))
    (fun _ n hn => v₁ n hn)
  have p₂ := p₁.trans o₂
  have k₂ := keep p₂
  obtain ⟨s₃, r₃, v₃, o₃⟩ := sbox_run k₂.1 k₂.2.1 (by decide : 3 < 4) t x (k₂.2.2 3 (by decide))
    (fun _ n hn => v₂ n hn)
  refine ⟨s₃, ?_, v₃, p₂.trans o₃⟩
  rw [f_eq]
  exact VG.AArch64.Tbl.runBlock_cat_some r₀ (VG.AArch64.Tbl.runBlock_cat_some r₁
    (VG.AArch64.Tbl.runBlock_cat_some r₂ (VG.AArch64.Tbl.runBlock_cat_some r₃ runBlock_nil)))

/-! ## The rotation -/

open VG.Proof.Blowfish.AArch64 (vword_uzp1 vword_uzp2 exec_vperm exec_vmov)

/-- The 64-bit product of two words. -/
def mulW (a b : Word) : BitVec 64 := a.setWidth 64 * b.setWidth 64

/-- What `umull` (`umull2` if `hi`) leaves. -/
def prodV (hi : Bool) (x m : BitVec 128) : BitVec 128 :=
  ofVDwords (mulW (vword x ((if hi then 2 else 0) + 0)) (vword m ((if hi then 2 else 0) + 0)))
    (mulW (vword x ((if hi then 2 else 0) + 1)) (vword m ((if hi then 2 else 0) + 1)))

theorem exec_umull (s : State) (hi : Bool) (d n m : VReg) :
    exec (.vop (.umull hi d n m)) s = some (s.setV d (prodV hi (s.v n) (s.v m))) := rfl

theorem exec_vorr (s : State) (d n m : VReg) :
    exec (.vop (.logic .orr d n m)) s = some (s.setV d (s.v n ||| s.v m)) := rfl

theorem prodF_words (x m : BitVec 128) {e : Nat} (he : e < 2) :
    vword (prodV false x m) (2 * e) = (mulW (vword x e) (vword m e)).extractLsb' 0 32 ∧
      vword (prodV false x m) (2 * e + 1) = (mulW (vword x e) (vword m e)).extractLsb' 32 32 := by
  rcases (by omega_using [he] : e = 0 ∨ e = 1) with rfl | rfl <;>
    exact ⟨by rw [prodV, vword_ofVDwords _ _ (by decide)]; rfl, by rw [prodV, vword_ofVDwords _ _ (by decide)]; rfl⟩

theorem prodT_words (x m : BitVec 128) {e : Nat} (he : e < 2) :
    vword (prodV true x m) (2 * e) = (mulW (vword x (2 + e)) (vword m (2 + e))).extractLsb' 0 32 ∧
      vword (prodV true x m) (2 * e + 1) = (mulW (vword x (2 + e)) (vword m (2 + e))).extractLsb' 32 32 := by
  rcases (by omega_using [he] : e = 0 ∨ e = 1) with rfl | rfl <;>
    exact ⟨by rw [prodV, vword_ofVDwords _ _ (by decide)]; rfl, by rw [prodV, vword_ofVDwords _ _ (by decide)]; rfl⟩

/-- What `rotl` leaves of the words `x`, for the multiplier `m`. -/
def rotV (x m : BitVec 128) : BitVec 128 :=
  VPermOp.eval .uzp1 .s4 (prodV false x m) (prodV true x m) |||
    VPermOp.eval .uzp2 .s4 (prodV false x m) (prodV true x m)

theorem vword_rotV (x m : BitVec 128) {r : Nat} (hr : r < 32)
    (hm : ∀ l < 4, vword m l = (1 : Word).rotateLeft r) {l : Nat} (hl : l < 4) :
    vword (rotV x m) l = (vword x l).rotateLeft r := by
  rw [rotV, vword_or, vword_uzp1 _ _ hl, vword_uzp2 _ _ hl]
  rcases (by omega_using [hl] : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
  · rw [ite_eq_left (by decide), ite_eq_left (by decide), (prodF_words x m (show 0 < 2 by decide)).1,
      (prodF_words x m (show 0 < 2 by decide)).2, hm 0 (by decide)]
    exact rot_mul _ hr
  · rw [ite_eq_left (by decide), ite_eq_left (by decide), (prodF_words x m (show 1 < 2 by decide)).1,
      (prodF_words x m (show 1 < 2 by decide)).2, hm 1 (by decide)]
    exact rot_mul _ hr
  · rw [ite_eq_right (by decide), ite_eq_right (by decide)]
    show vword (prodV true x m) (2 * 0) ||| vword (prodV true x m) (2 * 0 + 1) = _
    rw [(prodT_words x m (show 0 < 2 by decide)).1, (prodT_words x m (show 0 < 2 by decide)).2, hm 2 (by decide)]
    exact rot_mul _ hr
  · rw [ite_eq_right (by decide), ite_eq_right (by decide)]
    show vword (prodV true x m) (2 * 1) ||| vword (prodV true x m) (2 * 1 + 1) = _
    rw [(prodT_words x m (show 1 < 2 by decide)).1, (prodT_words x m (show 1 < 2 by decide)).2, hm 3 (by decide)]
    exact rot_mul _ hr

theorem fReg_ne_tmp : ∀ k < 4, fReg k ≠ .v0 ∧ fReg k ≠ .v1 ∧ fReg k ≠ .v20 ∧ fReg k ≠ .v21 ∧ fReg k ≠ mulReg := by
  decide

theorem rotl_run (s : State) {k : Nat} (hk : k < 4) :
    ∃ s', runBlock isa (rotl k) s = some s' ∧ s'.v (fReg k) = rotV (s.v (fReg k)) (s.v mulReg) ∧
      VOnly [.v0, .v1, .v20, .v21, fReg k] s s' := by
  have ne := fReg_ne_tmp k hk
  let s₁ := s.setV .v0 (prodV false (s.v (fReg k)) (s.v mulReg))
  let s₂ := s₁.setV .v1 (prodV true (s₁.v (fReg k)) (s₁.v mulReg))
  let s₃ := s₂.setV (outReg 0) (VPermOp.eval .uzp1 .s4 (s₂.v .v0) (s₂.v .v1))
  let s₄ := s₃.setV (outReg 1) (VPermOp.eval .uzp2 .s4 (s₃.v .v0) (s₃.v .v1))
  let s₅ := s₄.setV (fReg k) (s₄.v (outReg 0) ||| s₄.v (outReg 1))
  have a1 : s₁.v (fReg k) = s.v (fReg k) := v_setV_of_ne _ _ ne.1
  have m1 : s₁.v mulReg = s.v mulReg := v_setV_of_ne _ _ (by decide)
  have z2 : s₂.v .v0 = prodV false (s.v (fReg k)) (s.v mulReg) :=
    (v_setV_of_ne _ _ (by decide)).trans (v_setV_self _ _ _)
  have o2 : s₂.v .v1 = prodV true (s.v (fReg k)) (s.v mulReg) := by
    show (s₁.setV _ _).v _ = _
    rw [v_setV_self, a1, m1]
  have z3 : s₃.v .v0 = s₂.v .v0 := v_setV_of_ne _ _ (by decide)
  have o3 : s₃.v .v1 = s₂.v .v1 := v_setV_of_ne _ _ (by decide)
  have p3 : s₃.v (outReg 0) = VPermOp.eval .uzp1 .s4 (s₂.v .v0) (s₂.v .v1) := v_setV_self _ _ _
  have p4 : s₄.v (outReg 0) = s₃.v (outReg 0) := v_setV_of_ne _ _ (by decide)
  have q4 : s₄.v (outReg 1) = VPermOp.eval .uzp2 .s4 (s₃.v .v0) (s₃.v .v1) := v_setV_self _ _ _
  refine ⟨s₅, ?_, ?_, ?_⟩
  · rw [rotl, runBlock_cons, exec_umull, runStep_some, runBlock_cons, exec_umull, runStep_some, runBlock_cons,
      exec_vperm, runStep_some, runBlock_cons, exec_vperm, runStep_some, runBlock_cons, exec_vorr, runStep_some,
      runBlock_nil]
  · show (s₄.setV _ _).v _ = _
    rw [v_setV_self, p4, q4, p3, z3, o3, z2, o2, rotV]
  · exact ((((VOnly.setV s (by simp) _).trans (VOnly.setV _ (by simp) _)).trans
      (VOnly.setV _ (by simp [outReg]) _)).trans (VOnly.setV _ (by simp [outReg]) _)).trans (VOnly.setV _ (by simp) _)

/-- The registers the rotations write. -/
def rotRegs : List VReg := [.v0, .v1, .v20, .v21, .v12, .v13, .v14, .v15]

theorem rot_sub : ∀ k < 4, ∀ r ∈ [VReg.v0, .v1, .v20, .v21, fReg k], r ∈ rotRegs := by decide
theorem rot_other : ∀ k < 4, ∀ k' < 4, k ≠ k' → fReg k ∉ [VReg.v0, .v1, .v20, .v21, fReg k'] := by decide
theorem mul_notin : ∀ k < 4, mulReg ∉ [VReg.v0, .v1, .v20, .v21, fReg k] := by decide

theorem rotls_eq : (List.range 4).flatMap rotl = rotl 0 ++ (rotl 1 ++ (rotl 2 ++ (rotl 3 ++ []))) := rfl

theorem rotls_run (s : State) :
    ∃ s', runBlock isa ((List.range 4).flatMap rotl) s = some s' ∧
      (∀ k < 4, s'.v (fReg k) = rotV (s.v (fReg k)) (s.v mulReg)) ∧ VOnly rotRegs s s' := by
  obtain ⟨s₀, r₀, v₀, o₀⟩ := rotl_run s (show 0 < 4 by decide)
  obtain ⟨s₁, r₁, v₁, o₁⟩ := rotl_run s₀ (show 1 < 4 by decide)
  obtain ⟨s₂, r₂, v₂, o₂⟩ := rotl_run s₁ (show 2 < 4 by decide)
  obtain ⟨s₃, r₃, v₃, o₃⟩ := rotl_run s₂ (show 3 < 4 by decide)
  refine ⟨s₃, ?_, ?_, (((vmono o₀ (rot_sub 0 (by decide))).trans (vmono o₁ (rot_sub 1 (by decide)))).trans
    (vmono o₂ (rot_sub 2 (by decide)))).trans (vmono o₃ (rot_sub 3 (by decide)))⟩
  · rw [rotls_eq]
    exact VG.AArch64.Tbl.runBlock_cat_some r₀ (VG.AArch64.Tbl.runBlock_cat_some r₁
      (VG.AArch64.Tbl.runBlock_cat_some r₂ (VG.AArch64.Tbl.runBlock_cat_some r₃ runBlock_nil)))
  · have ro := rot_other
    have mn := mul_notin
    intro k hk
    rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · rw [o₃.2 _ (ro 0 (by decide) 3 (by decide) (by decide)), o₂.2 _ (ro 0 (by decide) 2 (by decide) (by decide)),
        o₁.2 _ (ro 0 (by decide) 1 (by decide) (by decide)), v₀]
    · rw [o₃.2 _ (ro 1 (by decide) 3 (by decide) (by decide)), o₂.2 _ (ro 1 (by decide) 2 (by decide) (by decide)),
        v₁, o₀.2 _ (ro 1 (by decide) 0 (by decide) (by decide)), o₀.2 _ (mn 0 (by decide))]
    · rw [o₃.2 _ (ro 2 (by decide) 3 (by decide) (by decide)), v₂,
        o₁.2 _ (ro 2 (by decide) 1 (by decide) (by decide)), o₀.2 _ (ro 2 (by decide) 0 (by decide) (by decide)),
        o₁.2 _ (mn 1 (by decide)), o₀.2 _ (mn 0 (by decide))]
    · rw [v₃, o₂.2 _ (ro 3 (by decide) 2 (by decide) (by decide)),
        o₁.2 _ (ro 3 (by decide) 1 (by decide) (by decide)), o₀.2 _ (ro 3 (by decide) 0 (by decide) (by decide)),
        o₂.2 _ (mn 2 (by decide)), o₁.2 _ (mn 1 (by decide)), o₀.2 _ (mn 0 (by decide))]

/-! ## The mask and the halves -/

theorem v0_ne_fReg : ∀ k < 4, VReg.v0 ≠ fReg k := by decide
theorem bReg_ne_fReg : ∀ k < 4, ∀ k' < 4, bReg k ≠ fReg k' := by decide
theorem aReg_ne_fReg : ∀ k < 4, ∀ k' < 4, aReg k ≠ fReg k' := by decide
theorem aReg_ne_bReg : ∀ k < 4, ∀ k' < 4, aReg k ≠ bReg k' := by decide
theorem aReg_inj : ∀ k < 4, ∀ k' < 4, k ≠ k' → aReg k ≠ aReg k' := by decide
theorem bReg_inj : ∀ k < 4, ∀ k' < 4, k ≠ k' → bReg k ≠ bReg k' := by decide

/-- `I = Kmᵢ op R`, `Kmᵢ` in every lane of `v0`. -/
theorem mask_run (s : State) (o : Op) :
    ∃ s', runBlock isa ((List.range 4).map fun k => o.instr (fReg k) .v0 (bReg k)) s = some s' ∧
      (∀ k < 4, s'.v (fReg k) = opV o (s.v .v0) (s.v (bReg k))) ∧ VOnly fRegs s s' := by
  refine map4_run s (fun k => o.instr (fReg k) .v0 (bReg k)) fReg (fun k v => opV o (v .v0) (v (bReg k)))
    (fun k _ u => exec_op _ _ _ _ _) fReg_ne (fun k hk v v' h => ?_)
  show opV o (v' .v0) (v' (bReg k)) = opV o (v .v0) (v (bReg k))
  rw [h .v0 fun k' hk' _ => v0_ne_fReg k' hk', h (bReg k) fun k' hk' _ => bReg_ne_fReg k hk k' hk']

theorem feistel_eq : feistel = ((List.range 4).map fun k => veor (fReg k) (aReg k) (fReg k)) ++
    ((List.range 4).map fun k => .vop (.mov (aReg k) (bReg k))) ++
    ((List.range 4).map fun k => .vop (.mov (bReg k) (fReg k))) := rfl

/-- `(L, R) := (R, L ^ f)`. -/
theorem feistel_run (s : State) :
    ∃ s', runBlock isa feistel s = some s' ∧ (∀ k < 4, s'.v (aReg k) = s.v (bReg k)) ∧
      (∀ k < 4, s'.v (bReg k) = s.v (aReg k) ^^^ s.v (fReg k)) ∧ VOnly (fRegs ++ halfRegs) s s' := by
  obtain ⟨s₁, r₁, v₁, o₁⟩ := map4_run s (fun k => veor (fReg k) (aReg k) (fReg k)) fReg
    (fun k v => v (aReg k) ^^^ v (fReg k)) (fun k _ u => rfl) fReg_ne (fun k hk v v' h => by
      show v' (aReg k) ^^^ v' (fReg k) = v (aReg k) ^^^ v (fReg k)
      rw [h (aReg k) fun k' hk' _ => aReg_ne_fReg k hk k' hk',
        h (fReg k) fun k' hk' hne => fReg_ne k hk k' hk' (Ne.symm hne)])
  obtain ⟨s₂, r₂, v₂, o₂⟩ := map4_run s₁ (fun k => .vop (.mov (aReg k) (bReg k))) aReg
    (fun k v => v (bReg k)) (fun k _ u => rfl) aReg_inj (fun k hk v v' h => by
      show v' (bReg k) = v (bReg k)
      exact h (bReg k) fun k' hk' _ => (aReg_ne_bReg k' hk' k hk).symm)
  obtain ⟨s₃, r₃, v₃, o₃⟩ := map4_run s₂ (fun k => .vop (.mov (bReg k) (fReg k))) bReg
    (fun k v => v (fReg k)) (fun k _ u => rfl) bReg_inj (fun k hk v v' h => by
      show v' (fReg k) = v (fReg k)
      exact h (fReg k) fun k' hk' _ => (bReg_ne_fReg k' hk' k hk).symm)
  have b₁ : ∀ k < 4, s₁.v (bReg k) = s.v (bReg k) := fun k hk => o₁.2 _ (by
    have := bReg_ne_fReg k hk; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨this 0 (by decide), this 1 (by decide), this 2 (by decide), this 3 (by decide)⟩)
  have f₂ : ∀ k < 4, s₂.v (fReg k) = s₁.v (fReg k) := fun k hk => o₂.2 _ (by
    have := aReg_ne_fReg; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨(this 0 (by decide) k hk).symm, (this 1 (by decide) k hk).symm, (this 2 (by decide) k hk).symm,
      (this 3 (by decide) k hk).symm⟩)
  have a₃ : ∀ k < 4, s₃.v (aReg k) = s₂.v (aReg k) := fun k hk => o₃.2 _ (by
    have := aReg_ne_bReg k hk; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨this 0 (by decide), this 1 (by decide), this 2 (by decide), this 3 (by decide)⟩)
  refine ⟨s₃, ?_, fun k hk => ?_, fun k hk => ?_, ((vmono o₁ (by decide)).trans (vmono o₂ (by decide))).trans
    (vmono o₃ (by decide))⟩
  · rw [feistel_eq]
    exact VG.AArch64.Tbl.runBlock_cat_some (VG.AArch64.Tbl.runBlock_cat_some r₁ r₂) r₃
  · rw [a₃ k hk, v₂ k hk, b₁ k hk]
  · rw [v₃ k hk, f₂ k hk, v₁ k hk]

/-! ## The subkeys -/

open VG.Impl.Cast5.AArch64 (rotate)
open VG.Proof.Cast5.AArch64 (rotate_ok)
open VG.Proof.Blowfish.AArch64 (exec_dup4)

theorem WP.exec_frame {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.syms = s.syms ∧ s'.sp = s.sp := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.syms he, Exec.sp he⟩

theorem low32 (x : Word) : (x.setWidth 64).setWidth 32 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

theorem vword_dup (w : Word) {l : Nat} (hl : l < 4) : vword (ofVWords w w w w) l = w := by
  rw [vword_ofVWords _ _ _ _ hl]
  rcases (by omega_using [hl] : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;> rfl

/-- The registers `subkeys` writes. -/
def subRegs : List Reg := [.x4, .x6, .x13, .x14, .x15]

/-- The others. -/
def keptRegs : List Reg :=
  [.x0, .x1, .x2, .x3, .x5, .x7, .x8, .x9, .x10, .x11, .x12, .x16, .x17, .x19, .x20, .x21, .x22, .x23, .x24,
   .x25, .x26, .x27, .x28, .x30]

theorem kept_of_notin : ∀ r : Reg, r ∉ subRegs → r ∈ keptRegs := by
  intro r; cases r <;> decide

theorem subkeys_ok {s : State} (h0 : InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 0) 4)
    (h64 : InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 64) 4) :
    WP isa (.block subkeys) s fun u =>
      (∀ l < 4, vword (u.v .v0) l = s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 0) 32) ∧
      (∀ l < 4, vword (u.v mulReg) l =
        (1 : Word).rotateLeft ((s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 64) 32).toNat % 32)) ∧
      RFrame subRegs [.v0, mulReg] s u := by
  let km := s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 0) 32
  let kr := s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 64) 32
  let s₁ := s.write .w .x6 km
  let s₂ := s₁.setV .v0 (let w := (s₁.gpr .x6).setWidth 32; ofVWords w w w w)
  let s₃ := s₂.write .w .x13 kr
  let s₄ := s₃.write .w .x4 ((1 : BitVec 16).setWidth 32)
  have h64' : InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .x5 + BitVec.ofNat 64 64) 4 := h64
  have e₃ : exec (.ldr .w .x13 .x5 64) s₂ = some s₃ := exec_ldr_w (by decide) h64'
  rw [subkeys, WP.block_append_iff, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₄, by
    rw [runBlock_cons, exec_ldr_w (by decide) h0, runStep_some, runBlock_cons, exec_dup4, runStep_some,
      runBlock_cons, e₃, runStep_some, runBlock_cons, exec_movz_w, runStep_some, runBlock_nil], ?_⟩
  have hax : s₄.gpr .x4 = (1 : Word).setWidth 64 := gpr_write_self _ _ _ _
  have h13 : s₄.gpr .x13 = kr.setWidth 64 :=
    (gpr_write_of_ne _ _ _ (by decide)).trans (gpr_write_self _ _ _ _)
  refine WP.mono (WP.gprs (WP.exec_frame (rotate_ok s₄ hax h13)) (rs := keptRegs) (by decide) (by decide)) ?_
  rintro u ⟨⟨⟨hx4, hmem, hrd, hwr, hv⟩, hsy, hsp⟩, hg⟩
  let u' := u.setV mulReg (let w := (u.gpr .x4).setWidth 32; ofVWords w w w w)
  refine WP.of_runBlock ⟨u', by rw [runBlock_cons, exec_dup4, runStep_some, runBlock_nil], ?_, ?_, ?_⟩
  · intro l hl
    show vword ((u.setV _ _).v .v0) l = km
    rw [v_setV_of_ne _ _ (by decide), hv]
    show vword (ofVWords _ _ _ _) l = km
    rw [vword_dup _ hl]
    show ((s.write .w .x6 km).gpr .x6).setWidth 32 = km
    rw [gpr_write_self]
    exact low32 km
  · intro l hl
    show vword ((u.setV _ _).v mulReg) l = _
    rw [v_setV_self]
    show vword (ofVWords _ _ _ _) l = _
    rw [vword_dup _ hl, hx4]
    exact low32 _
  · refine ⟨fun r hr => ?_, fun r hr => ?_, hmem, hrd, hwr, hsp, hsy⟩
    · simp only [subRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      show u.gpr r = s.gpr r
      rw [hg r (kept_of_notin r (by simp only [subRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]; exact hr))]
      show (s₃.write .w .x4 _).gpr r = _
      rw [gpr_write_of_ne _ _ _ hr.1]
      show (s₂.write .w .x13 _).gpr r = _
      rw [gpr_write_of_ne _ _ _ hr.2.2.1]
      show (s.write .w .x6 _).gpr r = _
      rw [gpr_write_of_ne _ _ _ hr.2.1]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      show (u.setV _ _).v r = s.v r
      rw [v_setV_of_ne _ _ hr.2, hv]
      exact v_setV_of_ne _ _ hr.1

/-! ## The round -/

/-- The vector registers a round writes before the halves trade places. -/
def preRegs : List VReg := rotRegs ++ planesRegs ++ stepRegs

/-- The vector registers a round writes. -/
def roundV : List VReg := .v27 :: preRegs ++ halfRegs

/-- The general-purpose registers a round writes. -/
def roundG : List Reg := [.x4, .x5, .x6, .x13, .x14, .x15]

theorem half_notin_pre : ∀ k < 4, aReg k ∉ preRegs ∧ bReg k ∉ preRegs ∧ aReg k ∉ [VReg.v0, mulReg] ∧
    bReg k ∉ [VReg.v0, mulReg] := by decide
theorem fReg_notin_planes : ∀ k < 4, fReg k ∉ planesRegs := by decide
theorem consts_notin : c64 ∉ preRegs ∧ c128 ∉ preRegs ∧ c64 ∉ [VReg.v0, mulReg] ∧ c128 ∉ [VReg.v0, mulReg] := by
  decide
theorem mul_notin_f : mulReg ∉ fRegs := by decide
theorem bReg_notin_f : ∀ k < 4, bReg k ∉ fRegs := by decide

theorem round_eq (t : Nat) (up : Bool) :
    round t up = subkeys ++ (((List.range 4).map fun k => (op t 0).instr (fReg k) .v0 (bReg k)) ++
      ((List.range 4).flatMap rotl ++ (planes fReg ++ (f t ++ (feistel ++
        [if up then .addImm .x .x5 .x5 4 else .subImm .x .x5 .x5 4]))))) := by
  simp only [round, List.append_assoc]

/-- Round `i`, of Type `t`, on the sixteen blocks: `(L, R) := (R, L ^ f(R, Kmᵢ, Krᵢ))`, the
subkeys read at `x5` and `x5 + 64`. -/
theorem round_ok {s : State} {t i : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) (hi : i % 3 = t % 3) (up : Bool)
    (h9 : s.gpr .x9 = s.syms planesSym) (hc : Consts s)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 0) 4)
    (h64 : InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 64) 4) :
    WP isa (.block (round t up)) s fun s' =>
      (∀ n < 16, lane s'.v aReg n = lane s.v bReg n) ∧
      (∀ n < 16, lane s'.v bReg n = lane s.v aReg n ^^^
        Spec.Cast5.f i (lane s.v bReg n) (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 0) 32)
          (s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 64) 32)) ∧
      s'.gpr .x5 = (if up then s.gpr .x5 + 4 else s.gpr .x5 - 4) ∧ RFrame roundG roundV s s' := by
  let km := s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 0) 32
  let kr := s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 64) 32
  have hr : kr.toNat % 32 < 32 := Nat.mod_lt _ (by decide)
  let I (n : Nat) : Word := (opEval (op t 0) km (lane s.v bReg n)).rotateLeft (kr.toNat % 32)
  rw [round_eq, WP.block_append_iff]
  refine WP.mono (subkeys_ok h0 h64) ?_
  rintro u ⟨hv0, hmul, fr⟩
  have hp := half_notin_pre
  obtain ⟨s₁, r₁, v₁, o₁⟩ := mask_run u (op t 0)
  obtain ⟨s₂, r₂, v₂, o₂⟩ := rotls_run s₁
  obtain ⟨s₃, r₃, v₃, o₃⟩ := planes_run s₂ fReg fReg_notin_planes
  have o₁₂ : VOnly preRegs u s₂ := (vmono o₁ (by decide)).trans (vmono o₂ (by decide))
  have o₁₃ : VOnly preRegs u s₃ := o₁₂.trans (vmono o₃ (by decide))
  have I₂ : ∀ n < 16, lane s₂.v fReg n = I n := by
    intro n hn
    have hk : n / 4 < 4 := by omega_using [hn]
    have hl : n % 4 < 4 := by omega_using []
    have hm₁ : ∀ l < 4, vword (s₁.v mulReg) l = (1 : Word).rotateLeft (kr.toNat % 32) := fun l hl => by
      rw [o₁.2 _ mul_notin_f]; exact hmul l hl
    simp only [lane]
    rw [v₂ _ hk, vword_rotV _ _ hr hm₁ hl, v₁ _ hk, vword_opV _ _ _ hl, hv0 _ hl, fr.v _ (hp _ hk).2.2.2]
    rfl
  have hx : ∀ j < 4, ∀ n < 16, vbyte (s₃.v (idxReg j)) n = Spec.Cast5.byte (I n) j := by
    intro j hj n hn
    rw [v₃ j hj n hn, vbyte_word _ (by omega_using [hj]), byte_eq, ← I₂ n hn]
    rfl
  have h9₃ : s₃.gpr .x9 = s₃.syms planesSym := by
    rw [o₁₃.gpr, o₁₃.1, fr.g _ (by decide)]
    show _ = u.syms planesSym
    rw [fr.syms]; exact h9
  have hc₃ : Consts s₃ :=
    ⟨fun e he => by rw [o₁₃.2 _ consts_notin.1, fr.v _ consts_notin.2.2.1]; exact hc.1 e he,
      fun e he => by rw [o₁₃.2 _ consts_notin.2.1, fr.v _ consts_notin.2.2.2]; exact hc.2 e he⟩
  obtain ⟨s₄, r₄, v₄, o₄⟩ := f_run h9₃ hc₃ t I hx
  have o₁₄ : VOnly preRegs u s₄ := o₁₃.trans (vmono o₄ (by decide))
  obtain ⟨s₅, r₅, va, vb, o₅⟩ := feistel_run s₄
  have o₁₅ : VOnly (preRegs ++ halfRegs) u s₅ := (vmono o₁₄ (by decide)).trans (vmono o₅ (by decide))
  let s₆ := s₅.write .x .x5 (if up then s₅.read .x .x5 + BitVec.ofNat _ 4 else s₅.read .x .x5 - BitVec.ofNat _ 4)
  have r₆ : runBlock isa [if up then .addImm .x .x5 .x5 4 else .subImm .x .x5 .x5 4] s₅ = some s₆ := by
    cases up
    · rw [runBlock_cons]; simp only [Bool.false_eq_true, ite_false]
      rw [exec_subImm_x (by decide), runStep_some, runBlock_nil]; rfl
    · rw [runBlock_cons]; simp only [ite_true]
      rw [exec_addImm_x (by decide), runStep_some, runBlock_nil]; rfl
  have cat := @VG.AArch64.Tbl.runBlock_cat_some
  refine WP.of_runBlock ⟨s₆, cat r₁ (cat r₂ (cat r₃ (cat r₄ (cat r₅ r₆)))), ?_, ?_, ?_, ?_⟩
  · intro n hn
    have hk : n / 4 < 4 := by omega_using [hn]
    simp only [lane]
    show vword (s₅.v _) _ = _
    rw [va _ hk, o₁₄.2 _ (hp _ hk).2.1, fr.v _ (hp _ hk).2.2.2]
  · intro n hn
    have hk : n / 4 < 4 := by omega_using [hn]
    have hf := v₄ n hn
    simp only [lane] at hf ⊢
    show vword (s₅.v _) _ = _
    rw [vb _ hk, Proof.Blowfish.AArch64.vword_xor, hf, o₁₄.2 _ (hp _ hk).1, fr.v _ (hp _ hk).2.2.1,
      f_eq_fAcc ht hi]
    rfl
  · show (s₅.write .x .x5 _).gpr .x5 = _
    rw [gpr_write_self]
    simp only [State.read, BitVec.setWidth_eq]
    rw [o₁₅.gpr, fr.g _ (by decide)]
    cases up <;> rfl
  · refine ⟨fun r hr => ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [roundG, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      show (s₅.write .x .x5 _).gpr r = _
      rw [gpr_write_of_ne _ _ _ hr.2.1, o₁₅.gpr, fr.g _ (by
        simp only [subRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hr.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2⟩)]
    · have h27 : r ≠ .v27 := fun h => hr (h ▸ List.mem_cons_self)
      have hrest : r ∉ preRegs ++ halfRegs := fun h => hr (List.mem_cons_of_mem _ h)
      show s₅.v r = _
      rw [o₁₅.2 _ hrest, fr.v _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨fun h => hrest (by subst h; decide), h27⟩)]
    · show s₅.mem = _
      rw [o₁₅.mem, fr.mem]
    · show s₅.rd = _
      rw [o₁₅.rd, fr.rd]
    · show s₅.wr = _
      rw [o₁₅.wr, fr.wr]
    · show s₅.sp = _
      rw [o₁₅.1, fr.sp]
    · show s₅.syms = _
      rw [o₁₅.1, fr.syms]

end VG.Proof.Cast5.AArch64.Tbl

import VerifiedGarbage.Proof.MdStream.Arm.Words
import VerifiedGarbage.Proof.Sha512.Word64
import VerifiedGarbage.Impl.Sha512.Arm
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Spill
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Sha512
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.Sha512.Arm.Stream

/- Proofs formerly in `VerifiedGarbage.Proof.Sha512.Arm.Word64`. -/
section

/-!
# 64-bit words as pairs of 32-bit halves, on ARMv7

The lemmas of `Proof/Sha512/Word64.lean` about the halves (`lo`, `hi`) of
64-bit words, stated for the ARMv7 implementation's `lo` and `hi` (the same
functions), and the terms of `Σ`/`σ` as the implementation lists them (`Op`).
-/

namespace VG.Proof.Sha512.Arm

open VG.Impl.Sha512.Arm (lo hi Op)

/-! ## Halves -/

theorem lo_toNat (x : BitVec 64) : (lo x).toNat = x.toNat % 2 ^ 32 := Word64.lo_toNat x

theorem hi_toNat (x : BitVec 64) : (hi x).toNat = x.toNat / 2 ^ 32 := Word64.hi_toNat x

@[simp] theorem lo_zero : lo 0#64 = 0#32 := rfl

@[simp] theorem hi_zero : hi 0#64 = 0#32 := rfl

theorem eq_of_lo_hi {x y : BitVec 64} (h1 : lo x = lo y) (h2 : hi x = hi y) : x = y :=
  Word64.eq_of_lo_hi h1 h2

theorem hi_append_lo (x : BitVec 64) : hi x ++ lo x = x := Word64.hi_append_lo x

theorem lo_append (a b : BitVec 32) : lo (a ++ b) = b := Word64.lo_append a b

theorem hi_append (a b : BitVec 32) : hi (a ++ b) = a := Word64.hi_append a b

theorem lo_add (x y : BitVec 64) : lo (x + y) = lo x + lo y := Word64.lo_add x y

theorem hi_add (x y : BitVec 64) :
    hi (x + y) = hi x + hi y + (if 2 ^ 32 ≤ (lo x).toNat + (lo y).toNat then 1 else 0) :=
  Word64.hi_add x y

theorem lo_xor (x y : BitVec 64) : lo (x ^^^ y) = lo x ^^^ lo y := Word64.lo_xor x y

theorem hi_xor (x y : BitVec 64) : hi (x ^^^ y) = hi x ^^^ hi y := Word64.hi_xor x y

theorem lo_and (x y : BitVec 64) : lo (x &&& y) = lo x &&& lo y := Word64.lo_and x y

theorem hi_and (x y : BitVec 64) : hi (x &&& y) = hi x &&& hi y := Word64.hi_and x y

theorem lo_or (x y : BitVec 64) : lo (x ||| y) = lo x ||| lo y := Word64.lo_or x y

theorem hi_or (x y : BitVec 64) : hi (x ||| y) = hi x ||| hi y := Word64.hi_or x y

theorem lo_rotr {n : Nat} (x : BitVec 64) (h0 : 0 < n) (h : n < 32) :
    lo (x.rotateRight n) = lo x >>> n ^^^ hi x <<< (32 - n) := Word64.lo_rotr x h0 h

theorem hi_rotr {n : Nat} (x : BitVec 64) (h0 : 0 < n) (h : n < 32) :
    hi (x.rotateRight n) = hi x >>> n ^^^ lo x <<< (32 - n) := Word64.hi_rotr x h0 h

theorem lo_rotr' {n : Nat} (x : BitVec 64) (h0 : 32 < n) (h : n < 64) :
    lo (x.rotateRight n) = hi x >>> (n - 32) ^^^ lo x <<< (64 - n) := Word64.lo_rotr' x h0 h

theorem hi_rotr' {n : Nat} (x : BitVec 64) (h0 : 32 < n) (h : n < 64) :
    hi (x.rotateRight n) = lo x >>> (n - 32) ^^^ hi x <<< (64 - n) := Word64.hi_rotr' x h0 h

theorem lo_shr {n : Nat} (x : BitVec 64) (h0 : 0 < n) (h : n < 32) :
    lo (x >>> n) = lo x >>> n ^^^ hi x <<< (32 - n) := Word64.lo_shr x h0 h

theorem hi_shr (n : Nat) (x : BitVec 64) : hi (x >>> n) = hi x >>> n := Word64.hi_shr n x

/-! ## The terms of `Σ₀`, `Σ₁`, `σ₀` and `σ₁` -/

/-- A term's value. -/
def _root_.VG.Impl.Sha512.Arm.Op.eval (x : BitVec 64) : Op → BitVec 64
  | .rotr n => x.rotateRight n
  | .shr n => x >>> n

/-- The shift amounts that the code can encode. -/
def _root_.VG.Impl.Sha512.Arm.Op.valid : Op → Bool
  | .rotr n => 0 < n && n < 64 && n != 32
  | .shr n => 0 < n && n < 32

/-- The exclusive or of the terms. -/
def evalOps (x : BitVec 64) (ops : List Op) : BitVec 64 := ops.foldl (fun a o => a ^^^ o.eval x) 0

/-- The values of the parts of a term's low half, from the halves `L`, `H`. -/
def _root_.VG.Impl.Sha512.Arm.Op.loVals (L H : BitVec 32) : Op → List (BitVec 32)
  | .rotr n => if n < 32 then [L >>> n, H <<< (32 - n)] else [H >>> (n - 32), L <<< (64 - n)]
  | .shr n => [L >>> n, H <<< (32 - n)]

/-- The values of the parts of a term's high half. -/
def _root_.VG.Impl.Sha512.Arm.Op.hiVals (L H : BitVec 32) : Op → List (BitVec 32)
  | .rotr n => if n < 32 then [H >>> n, L <<< (32 - n)] else [L >>> (n - 32), H <<< (64 - n)]
  | .shr n => [H >>> n]

/-- The term, as a `Word64.Term` (whose value, validity and parts are the same). -/
def _root_.VG.Impl.Sha512.Arm.Op.term : Op → Word64.Term
  | .rotr n => .rotr n
  | .shr n => .shr n

theorem evalOps_term (x : BitVec 64) (ops : List Op) :
    VG.Proof.Sha512.Arm.evalOps x ops = Word64.evalOps x (ops.map Op.term) := by
  have e : (fun a (o : Op) => a ^^^ o.eval x) = fun a o => a ^^^ o.term.eval x :=
    funext fun _ => funext fun o => by cases o <;> rfl
  rw [VG.Proof.Sha512.Arm.evalOps, Word64.evalOps, List.foldl_map, e]

theorem valid_term {ops : List Op} (hv : ∀ o ∈ ops, o.valid = true) :
    ∀ o ∈ ops.map Op.term, o.valid = true := by
  intro o ho
  obtain ⟨o', h', rfl⟩ := List.mem_map.mp ho
  cases o' <;> exact hv _ h'

theorem flatMap_loVals (L H : BitVec 32) (ops : List Op) :
    ops.flatMap (Op.loVals L H) = (ops.map Op.term).flatMap (Word64.Term.loVals L H) := by
  induction ops with
  | nil => rfl
  | cons o os ih =>
    rw [List.flatMap_cons, List.map_cons, List.flatMap_cons, ih]
    cases o <;> rfl

theorem flatMap_hiVals (L H : BitVec 32) (ops : List Op) :
    ops.flatMap (Op.hiVals L H) = (ops.map Op.term).flatMap (Word64.Term.hiVals L H) := by
  induction ops with
  | nil => rfl
  | cons o os ih =>
    rw [List.flatMap_cons, List.map_cons, List.flatMap_cons, ih]
    cases o <;> rfl

theorem lo_evalOps (x : BitVec 64) (ops : List Op) (hv : ∀ o ∈ ops, o.valid = true) :
    (ops.flatMap (Op.loVals (lo x) (hi x))).foldl (· ^^^ ·) 0 = lo (VG.Proof.Sha512.Arm.evalOps x ops) := by
  rw [VG.Proof.Sha512.Arm.flatMap_loVals, VG.Proof.Sha512.Arm.evalOps_term]
  exact Word64.lo_evalOps x _ (VG.Proof.Sha512.Arm.valid_term hv)

theorem hi_evalOps (x : BitVec 64) (ops : List Op) (hv : ∀ o ∈ ops, o.valid = true) :
    (ops.flatMap (Op.hiVals (lo x) (hi x))).foldl (· ^^^ ·) 0 = hi (VG.Proof.Sha512.Arm.evalOps x ops) := by
  rw [VG.Proof.Sha512.Arm.flatMap_hiVals, VG.Proof.Sha512.Arm.evalOps_term]
  exact Word64.hi_evalOps x _ (VG.Proof.Sha512.Arm.valid_term hv)

theorem bsig0_eq (x : BitVec 64) : Spec.Sha512.bsig0 x = VG.Proof.Sha512.Arm.evalOps x Impl.Sha512.Arm.bsig0 := by
  simp [VG.Proof.Sha512.Arm.evalOps, Impl.Sha512.Arm.bsig0, Spec.Sha512.bsig0, Op.eval]

theorem bsig1_eq (x : BitVec 64) : Spec.Sha512.bsig1 x = VG.Proof.Sha512.Arm.evalOps x Impl.Sha512.Arm.bsig1 := by
  simp [VG.Proof.Sha512.Arm.evalOps, Impl.Sha512.Arm.bsig1, Spec.Sha512.bsig1, Op.eval]

theorem ssig0_eq (x : BitVec 64) : Spec.Sha512.ssig0 x = VG.Proof.Sha512.Arm.evalOps x Impl.Sha512.Arm.ssig0 := by
  simp [VG.Proof.Sha512.Arm.evalOps, Impl.Sha512.Arm.ssig0, Spec.Sha512.ssig0, Op.eval]

theorem ssig1_eq (x : BitVec 64) : Spec.Sha512.ssig1 x = VG.Proof.Sha512.Arm.evalOps x Impl.Sha512.Arm.ssig1 := by
  simp [VG.Proof.Sha512.Arm.evalOps, Impl.Sha512.Arm.ssig1, Spec.Sha512.ssig1, Op.eval]

/-! ## Words in memory -/

theorem readW_lo (m : Mem) (a : Addr) : lo (m.readW a 64) = m.readW a 32 := Word64.readW_lo m a

theorem readW_hi (m : Mem) (a : Addr) : hi (m.readW a 64) = m.readW (a + 4) 32 := Word64.readW_hi m a

/-- A 64-bit word in memory is its high half at `a + 4` and its low half at `a`. -/
theorem readW64 (m : Mem) (a : Addr) : m.readW a 64 = m.readW (a + 4) 32 ++ m.readW a 32 :=
  Word64.readW64 m a

end VG.Proof.Sha512.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha512.Arm.Rounds`. -/
section

/-!
# SHA-512 on ARMv7: the 64-bit operations

Weakest-precondition rules for the macros of `VG.Impl.Sha512.Arm` (loads and
stores of a 64-bit word, 64-bit additions, constants, `Σ`/`σ`, `Ch` and
`Maj`), each proved once for any registers and offsets, in
continuation-passing style: the rule for `x` proves `WP (x ++ rest)` from a
proof of `WP rest` for every state `x` can end in.
-/

namespace VG.Proof.Sha512.Arm

open VG VG.Arm VG.Impl.Sha512.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd WP.cons wp_mov wp_and wp_orr wp_ldr wp_str wp_rev op2_reg)

/-! ## States -/

/-- `s'` is `s` with (at most) the registers `ds` changed (and the flags). -/
structure Only (ds : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ ds → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Only.refl (ds : List Reg) (s : State) : VG.Proof.Sha512.Arm.Only ds s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem Only.of_upd {s s' : State} {d : Reg} {v : BitVec 32} (u : Upd s s' d v) : VG.Proof.Sha512.Arm.Only [d] s s' :=
  ⟨fun r h => u.other r (by simpa using h), u.mem, u.rd, u.wr, u.sp⟩

theorem Only.trans {ds es : List Reg} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.Sha512.Arm.Only ds s₁ s₂) (h₂ : VG.Proof.Sha512.Arm.Only es s₂ s₃) :
    VG.Proof.Sha512.Arm.Only (ds ++ es) s₁ s₃ :=
  ⟨fun r h => by
    simp only [List.mem_append, not_or] at h
    rw [h₂.gpr r h.2, h₁.gpr r h.1], h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₂.sp.trans h₁.sp⟩

theorem Only.mono {ds es : List Reg} {s s' : State} (h : VG.Proof.Sha512.Arm.Only ds s s') (he : ∀ r ∈ ds, r ∈ es) :
    VG.Proof.Sha512.Arm.Only es s s' :=
  ⟨fun r hr => h.gpr r fun hd => hr (he r hd), h.mem, h.rd, h.wr, h.sp⟩

/-- The 64-bit word `x` is in the registers `l` (low half) and `h`. -/
def Pair (s : State) (l h : Reg) (x : BitVec 64) : Prop := s.gpr l = lo x ∧ s.gpr h = hi x

theorem Pair.of_only {ds : List Reg} {s s' : State} {l h : Reg} {x : BitVec 64} (p : VG.Proof.Sha512.Arm.Pair s l h x)
    (o : VG.Proof.Sha512.Arm.Only ds s s') (hl : l ∉ ds) (hh : h ∉ ds) : VG.Proof.Sha512.Arm.Pair s' l h x :=
  ⟨(o.gpr l hl).trans p.1, (o.gpr h hh).trans p.2⟩

/-! ## Memory -/

/-- The address `b + off`. -/
abbrev A (b : BitVec 32) (off : Nat) : Addr := State.addr (b + BitVec.ofNat 32 off)

/-- The 64-bit word at `b + off`, from its two halves. -/
def rd64 (m : Mem) (b : BitVec 32) (off : Nat) : BitVec 64 :=
  m.readW (VG.Proof.Sha512.Arm.A b (off + 4)) 32 ++ m.readW (VG.Proof.Sha512.Arm.A b off) 32

/-- Store the 64-bit word `x` at `b + off`, as its two halves. -/
def write64 (m : Mem) (b : BitVec 32) (off : Nat) (x : BitVec 64) : Mem :=
  (m.writeW (VG.Proof.Sha512.Arm.A b off) (lo x)).writeW (VG.Proof.Sha512.Arm.A b (off + 4)) (hi x)

theorem lo_rd64 (m : Mem) (b : BitVec 32) (off : Nat) : lo (VG.Proof.Sha512.Arm.rd64 m b off) = m.readW (VG.Proof.Sha512.Arm.A b off) 32 :=
  VG.Proof.Sha512.Arm.lo_append _ _

theorem hi_rd64 (m : Mem) (b : BitVec 32) (off : Nat) :
    hi (VG.Proof.Sha512.Arm.rd64 m b off) = m.readW (VG.Proof.Sha512.Arm.A b (off + 4)) 32 :=
  VG.Proof.Sha512.Arm.hi_append _ _

theorem mem_rd {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n :=
  let ⟨r, hr, hc⟩ := h
  ⟨r, List.mem_append_right _ hr, hc⟩

/-! ## Single instructions not covered by the SHA-256 rules -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_eor {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .eor d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n ^^^ y)) (by simp [exec, ho]) (k _ (Upd.setReg _ _ _))

theorem wp_adds {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n + y) → s'.c = decide (2 ^ 32 ≤ (s.gpr n).toNat + y.toNat) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.adds d n o :: is)) s Q :=
  WP.cons (s' := (addFlags s (s.gpr n) y).setReg d (s.gpr n + y)) (by simp [exec, ho])
    (k _ ⟨by simp [State.setReg], fun r h => by simp [State.setReg, addFlags, h], rfl, rfl, rfl, rfl⟩
      rfl)

theorem wp_adc {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n + y + (if s.c then 1 else 0)) → WP isa (.block is) s' Q) :
    WP isa (.block (.adc d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n + y + (if s.c then 1 else 0))) (by simp [exec, ho])
    (k _ (Upd.setReg _ _ _))

theorem wp_movw {d : Reg} {v : BitVec 16}
    (k : ∀ s', Upd s s' d (v.setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movw d v :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_movt {d : Reg} {v : BitVec 16}
    (k : ∀ s', Upd s s' d (v ++ (s.gpr d).extractLsb' 0 16 : BitVec 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movt d v :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

end

/-! ## Loads, stores, additions and constants -/

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

theorem wp_ld {l h b : Reg} {B : BitVec 32} {off : Nat} (hlb : l ≠ b) (hlh : l ≠ h)
    (ho : off + 4 < 4096) (hb : s.gpr b = B)
    (hi : InRegions s.wr (VG.Proof.Sha512.Arm.A B off) 4) (hi' : InRegions s.wr (VG.Proof.Sha512.Arm.A B (off + 4)) 4)
    (k : ∀ s', VG.Proof.Sha512.Arm.Only [l, h] s s' → VG.Proof.Sha512.Arm.Pair s' l h (VG.Proof.Sha512.Arm.rd64 s.mem B off) → WP isa (.block rest) s' Q) :
    WP isa (.block (ld l h b off ++ rest)) s Q := by
  simp only [ld, List.cons_append, List.nil_append]
  refine wp_ldr (by omega) (by rw [hb]) (VG.Proof.Sha512.Arm.mem_rd hi) fun s₁ u₁ => ?_
  refine wp_ldr ho (by rw [u₁.other b (Ne.symm hlb), hb]) (by rw [u₁.rd, u₁.wr]; exact VG.Proof.Sha512.Arm.mem_rd hi')
    fun s₂ u₂ => k s₂ ((Only.of_upd u₁).trans (Only.of_upd u₂)) ⟨?_, ?_⟩
  · rw [u₂.other l hlh, u₁.gpr, VG.Proof.Sha512.Arm.lo_rd64]
  · rw [u₂.gpr, u₁.mem, VG.Proof.Sha512.Arm.hi_rd64]

theorem wp_st {l h b : Reg} {B : BitVec 32} {off : Nat} {x : BitVec 64}
    (ho : off + 4 < 4096) (hb : s.gpr b = B) (hp : VG.Proof.Sha512.Arm.Pair s l h x)
    (hi : InRegions s.wr (VG.Proof.Sha512.Arm.A B off) 4) (hi' : InRegions s.wr (VG.Proof.Sha512.Arm.A B (off + 4)) 4)
    (k : ∀ s', Mupd s s' (VG.Proof.Sha512.Arm.write64 s.mem B off x) → WP isa (.block rest) s' Q) :
    WP isa (.block (VG.Impl.Sha512.Arm.st l h b off ++ rest)) s Q := by
  simp only [VG.Impl.Sha512.Arm.st, List.cons_append, List.nil_append]
  refine wp_str (by omega) (by rw [hb]) hi fun s₁ u₁ => ?_
  refine wp_str ho (by rw [u₁.gpr, hb]) (by rw [u₁.wr]; exact hi') fun s₂ u₂ =>
    k s₂ ⟨u₂.gpr.trans u₁.gpr, ?_, u₂.rd.trans u₁.rd, u₂.wr.trans u₁.wr, u₂.sp.trans u₁.sp⟩
  rw [u₂.mem, u₁.mem, u₁.gpr, hp.1, hp.2]; rfl

theorem carry_eq (a b : BitVec 32) :
    (if decide (2 ^ 32 ≤ a.toNat + b.toNat) = true then (1 : BitVec 32) else 0) =
      if 2 ^ 32 ≤ a.toNat + b.toNat then 1 else 0 := by
  simp only [decide_eq_true_eq]

theorem wp_add64 {dl dh l h : Reg} {x y : BitVec 64} (h₁ : dl ≠ dh) (h₂ : dl ≠ h)
    (px : VG.Proof.Sha512.Arm.Pair s dl dh x) (py : VG.Proof.Sha512.Arm.Pair s l h y)
    (k : ∀ s', VG.Proof.Sha512.Arm.Only [dl, dh] s s' → VG.Proof.Sha512.Arm.Pair s' dl dh (x + y) → WP isa (.block rest) s' Q) :
    WP isa (.block (add64 dl dh l h ++ rest)) s Q := by
  simp only [add64, List.cons_append, List.nil_append]
  refine VG.Proof.Sha512.Arm.wp_adds (op2_reg _ _) fun s₁ u₁ hc => ?_
  refine VG.Proof.Sha512.Arm.wp_adc (op2_reg _ _) fun s₂ u₂ => k s₂ ((Only.of_upd u₁).trans (Only.of_upd u₂)) ⟨?_, ?_⟩
  · rw [u₂.other dl h₁, u₁.gpr, px.1, py.1, VG.Proof.Sha512.Arm.lo_add]
  · rw [u₂.gpr, hc, VG.Proof.Sha512.Arm.carry_eq, u₁.other dh (Ne.symm h₁), u₁.other h (Ne.symm h₂), px.1, py.1, px.2,
      py.2, VG.Proof.Sha512.Arm.hi_add]

theorem movw_movt' (x : BitVec 32) :
    (x.extractLsb' 16 16 ++ ((x.extractLsb' 0 16).setWidth 32).extractLsb' 0 16 : BitVec 32) = x :=
  movw_movt x

theorem wp_const64 {l h : Reg} {x : BitVec 64} (hlh : l ≠ h)
    (k : ∀ s', VG.Proof.Sha512.Arm.Only [l, h] s s' → VG.Proof.Sha512.Arm.Pair s' l h x → WP isa (.block rest) s' Q) :
    WP isa (.block (const64 l h x ++ rest)) s Q := by
  simp only [const64, List.cons_append, List.nil_append]
  refine VG.Proof.Sha512.Arm.wp_movw fun s₁ u₁ => VG.Proof.Sha512.Arm.wp_movt fun s₂ u₂ => VG.Proof.Sha512.Arm.wp_movw fun s₃ u₃ => VG.Proof.Sha512.Arm.wp_movt fun s₄ u₄ =>
    k s₄ ((((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans
      (Only.of_upd u₄) |>.mono (by simp)) ⟨?_, ?_⟩
  · rw [u₄.other l hlh, u₃.other l hlh, u₂.gpr, u₁.gpr, movw_movt]
  · rw [u₄.gpr, u₃.gpr, movw_movt]

end

/-! ## Exclusive ors of shifted registers -/

/-- The value of an operand (`0` if it cannot be encoded). -/
def val (s : State) (o : Op2) : BitVec 32 := (o.eval s).getD 0

/-- An operand that is a shift of a register other than `d`, by an encodable amount. -/
def OkOp (d : Reg) : Op2 → Prop
  | .shifted r _ n => r ≠ d ∧ 1 ≤ n ∧ n ≤ 31
  | _ => False

theorem OkOp.eval {d : Reg} {o : Op2} (h : VG.Proof.Sha512.Arm.OkOp d o) {s s₀ : State}
    (hs : ∀ r, r ≠ d → s.gpr r = s₀.gpr r) : o.eval s = some (VG.Proof.Sha512.Arm.val s₀ o) := by
  match o, h with
  | .shifted r sh n, ⟨hr, h1, h2⟩ =>
    simp only [VG.Proof.Sha512.Arm.val, Op2.eval, h1, h2, and_self, ite_true, hs r hr, Option.getD_some]

section
variable {rest : List Instr} {Q : State → Prop}

theorem wp_eors {d : Reg} (s₀ : State) (ps : List Op2) (hp : ∀ p ∈ ps, VG.Proof.Sha512.Arm.OkOp d p) :
    ∀ (s : State) (acc : BitVec 32), (∀ r, r ≠ d → s.gpr r = s₀.gpr r) → s.gpr d = acc →
    (∀ s', VG.Proof.Sha512.Arm.Only [d] s s' → s'.gpr d = (ps.map (VG.Proof.Sha512.Arm.val s₀)).foldl (· ^^^ ·) acc →
      WP isa (.block rest) s' Q) →
    WP isa (.block (ps.map (fun p => Instr.dp .eor d d p) ++ rest)) s Q := by
  induction ps with
  | nil => intro s acc _ hd k; exact k s (Only.refl _ _) hd
  | cons p ps ih =>
    intro s acc hs hd k
    simp only [List.map_cons, List.cons_append]
    refine VG.Proof.Sha512.Arm.wp_eor ((hp p (by simp)).eval hs) fun s₁ u₁ => ?_
    refine ih (fun q hq => hp q (by simp [hq])) s₁ _ (fun r hr => by rw [u₁.other r hr, hs r hr])
      u₁.gpr fun s' o h => k s' ((Only.of_upd u₁).trans o |>.mono (by simp)) ?_
    rw [h, hd]; rfl

theorem wp_xorOf {d : Reg} (ps : List Op2) (hne : ps ≠ []) (hp : ∀ p ∈ ps, VG.Proof.Sha512.Arm.OkOp d p) (s : State)
    (k : ∀ s', VG.Proof.Sha512.Arm.Only [d] s s' → s'.gpr d = (ps.map (VG.Proof.Sha512.Arm.val s)).foldl (· ^^^ ·) 0 →
      WP isa (.block rest) s' Q) :
    WP isa (.block (xorOf d ps ++ rest)) s Q := by
  match ps, hne with
  | p :: ps, _ =>
    simp only [xorOf, List.cons_append]
    refine wp_mov ((hp p (by simp)).eval (s₀ := s) fun _ _ => rfl) fun s₁ u₁ => ?_
    refine VG.Proof.Sha512.Arm.wp_eors s ps (fun q hq => hp q (by simp [hq])) s₁ _ (fun r hr => u₁.other r hr) u₁.gpr
      fun s' o h => k s' ((Only.of_upd u₁).trans o |>.mono (by simp)) ?_
    rw [h, List.map_cons, List.foldl_cons]
    congr 1
    simp

end

/-! ## `Σ₀`, `Σ₁`, `σ₀`, `σ₁` -/

theorem Op.okLo {l h d : Reg} (hl : l ≠ d) (hh : h ≠ d) {o : Op} (hv : o.valid = true) :
    ∀ p ∈ o.lo l h, VG.Proof.Sha512.Arm.OkOp d p := by
  cases o with
  | rotr n =>
    simp only [Op.valid, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hv
    simp only [Op.lo]
    split <;> simp only [List.mem_cons, List.not_mem_nil, or_false] <;>
      rintro p (rfl | rfl) <;> exact ⟨by assumption, by omega, by omega⟩
  | shr n =>
    simp only [Op.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    simp only [Op.lo, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl) <;> exact ⟨by assumption, by omega, by omega⟩

theorem Op.okHi {l h d : Reg} (hl : l ≠ d) (hh : h ≠ d) {o : Op} (hv : o.valid = true) :
    ∀ p ∈ o.hi l h, VG.Proof.Sha512.Arm.OkOp d p := by
  cases o with
  | rotr n =>
    simp only [Op.valid, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hv
    simp only [Op.hi]
    split <;> simp only [List.mem_cons, List.not_mem_nil, or_false] <;>
      rintro p (rfl | rfl) <;> exact ⟨by assumption, by omega, by omega⟩
  | shr n =>
    simp only [Op.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    simp only [Op.hi, List.mem_cons, List.not_mem_nil, or_false]
    rintro p rfl; exact ⟨by assumption, by omega, by omega⟩

theorem Op.valLo (s : State) (l h : Reg) {o : Op} (hv : o.valid = true) :
    (o.lo l h).map (VG.Proof.Sha512.Arm.val s) = o.loVals (s.gpr l) (s.gpr h) := by
  cases o with
  | rotr n =>
    simp only [Op.valid, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hv
    simp only [Op.lo, Op.loVals]
    split
    · simp [VG.Proof.Sha512.Arm.val, Op2.eval, show 1 ≤ n by omega, show 1 ≤ 32 - n by omega,
        show 32 - n ≤ 31 by omega, show n ≤ 31 by omega]
    · simp [VG.Proof.Sha512.Arm.val, Op2.eval, show 1 ≤ n - 32 by omega, show n - 32 ≤ 31 by omega,
        show 1 ≤ 64 - n by omega, show 64 - n ≤ 31 by omega]
  | shr n =>
    simp only [Op.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    simp [Op.lo, Op.loVals, VG.Proof.Sha512.Arm.val, Op2.eval, show 1 ≤ n by omega, show 1 ≤ 32 - n by omega,
      show 32 - n ≤ 31 by omega, show n ≤ 31 by omega]

theorem Op.valHi (s : State) (l h : Reg) {o : Op} (hv : o.valid = true) :
    (o.hi l h).map (VG.Proof.Sha512.Arm.val s) = o.hiVals (s.gpr l) (s.gpr h) := by
  cases o with
  | rotr n =>
    simp only [Op.valid, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hv
    simp only [Op.hi, Op.hiVals]
    split
    · simp [VG.Proof.Sha512.Arm.val, Op2.eval, show 1 ≤ n by omega, show 1 ≤ 32 - n by omega,
        show 32 - n ≤ 31 by omega, show n ≤ 31 by omega]
    · simp [VG.Proof.Sha512.Arm.val, Op2.eval, show 1 ≤ n - 32 by omega, show n - 32 ≤ 31 by omega,
        show 1 ≤ 64 - n by omega, show 64 - n ≤ 31 by omega]
  | shr n =>
    simp only [Op.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    simp [Op.hi, Op.hiVals, VG.Proof.Sha512.Arm.val, Op2.eval, show 1 ≤ n by omega, show n ≤ 31 by omega]

theorem flatMap_ne_nil {ops : List Op} (h : ops ≠ []) (f : Op → List Op2)
    (hf : ∀ o, f o ≠ []) : ops.flatMap f ≠ [] := by
  match ops, h with
  | o :: _, _ => simp [hf o]

theorem Op.lo_ne_nil (l h : Reg) (o : Op) : o.lo l h ≠ [] := by
  cases o <;> simp only [Op.lo] <;> (try split) <;> simp

theorem Op.hi_ne_nil (l h : Reg) (o : Op) : o.hi l h ≠ [] := by
  cases o <;> simp only [Op.hi] <;> (try split) <;> simp

theorem map_val_lo (s : State) (l h : Reg) {ops : List Op} (hv : ∀ o ∈ ops, o.valid = true) :
    (ops.flatMap (Op.lo l h)).map (VG.Proof.Sha512.Arm.val s) = ops.flatMap (Op.loVals (s.gpr l) (s.gpr h)) := by
  induction ops with
  | nil => rfl
  | cons o os ih =>
    rw [List.flatMap_cons, List.flatMap_cons, List.map_append, Op.valLo s l h (hv o (by simp)),
      ih fun o' h' => hv o' (by simp [h'])]

theorem map_val_hi (s : State) (l h : Reg) {ops : List Op} (hv : ∀ o ∈ ops, o.valid = true) :
    (ops.flatMap (Op.hi l h)).map (VG.Proof.Sha512.Arm.val s) = ops.flatMap (Op.hiVals (s.gpr l) (s.gpr h)) := by
  induction ops with
  | nil => rfl
  | cons o os ih =>
    rw [List.flatMap_cons, List.flatMap_cons, List.map_append, Op.valHi s l h (hv o (by simp)),
      ih fun o' h' => hv o' (by simp [h'])]

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

theorem wp_sig {dl dh l h : Reg} {x : BitVec 64} {ops : List Op} (hne : ops ≠ [])
    (hv : ∀ o ∈ ops, o.valid = true) (hd : dl ≠ dh)
    (h₁ : l ≠ dl) (h₂ : h ≠ dl) (h₃ : l ≠ dh) (h₄ : h ≠ dh) (hp : VG.Proof.Sha512.Arm.Pair s l h x)
    (k : ∀ s', VG.Proof.Sha512.Arm.Only [dl, dh] s s' → VG.Proof.Sha512.Arm.Pair s' dl dh (VG.Proof.Sha512.Arm.evalOps x ops) → WP isa (.block rest) s' Q) :
    WP isa (.block (sig dl dh l h ops ++ rest)) s Q := by
  simp only [sig, List.append_assoc]
  refine VG.Proof.Sha512.Arm.wp_xorOf _ (VG.Proof.Sha512.Arm.flatMap_ne_nil hne _ (Op.lo_ne_nil l h))
    (fun p hp' => by
      obtain ⟨o, ho, hp'⟩ := List.mem_flatMap.mp hp'
      exact Op.okLo h₁ h₂ (hv o ho) p hp') s fun s₁ o₁ e₁ => ?_
  refine VG.Proof.Sha512.Arm.wp_xorOf _ (VG.Proof.Sha512.Arm.flatMap_ne_nil hne _ (Op.hi_ne_nil l h))
    (fun p hp' => by
      obtain ⟨o, ho, hp'⟩ := List.mem_flatMap.mp hp'
      exact Op.okHi h₃ h₄ (hv o ho) p hp') s₁ fun s₂ o₂ e₂ => k s₂ (o₁.trans o₂) ⟨?_, ?_⟩
  · rw [o₂.gpr dl (by simpa using hd), e₁, VG.Proof.Sha512.Arm.map_val_lo s l h hv, hp.1, hp.2, VG.Proof.Sha512.Arm.lo_evalOps x ops hv]
  · rw [e₂, VG.Proof.Sha512.Arm.map_val_hi s₁ l h hv, o₁.gpr l (by simpa using h₁), o₁.gpr h (by simpa using h₂), hp.1,
      hp.2, VG.Proof.Sha512.Arm.hi_evalOps x ops hv]

end

/-! ## `Ch` and `Maj` -/

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

theorem wp_ld1 {t b : Reg} {B : BitVec 32} {off : Nat} (ho : off < 4096) (hb : s.gpr b = B)
    (hi : InRegions s.wr (VG.Proof.Sha512.Arm.A B off) 4)
    (k : ∀ s', VG.Proof.Sha512.Arm.Only [t] s s' → s'.gpr t = s.mem.readW (VG.Proof.Sha512.Arm.A B off) 32 → WP isa (.block rest) s' Q) :
    WP isa (.block (.ldr t b off :: rest)) s Q :=
  wp_ldr ho (by rw [hb]) (VG.Proof.Sha512.Arm.mem_rd hi) fun s' u => k s' (Only.of_upd u) u.gpr

theorem wp_eor1 {d n m : Reg}
    (k : ∀ s', VG.Proof.Sha512.Arm.Only [d] s s' → s'.gpr d = s.gpr n ^^^ s.gpr m → WP isa (.block rest) s' Q) :
    WP isa (.block (.dp .eor d n (.reg m) :: rest)) s Q :=
  VG.Proof.Sha512.Arm.wp_eor (op2_reg _ _) fun s' u => k s' (Only.of_upd u) u.gpr

theorem wp_and1 {d n m : Reg}
    (k : ∀ s', VG.Proof.Sha512.Arm.Only [d] s s' → s'.gpr d = s.gpr n &&& s.gpr m → WP isa (.block rest) s' Q) :
    WP isa (.block (.dp .and d n (.reg m) :: rest)) s Q :=
  wp_and (op2_reg _ _) fun s' u => k s' (Only.of_upd u) u.gpr

theorem wp_orr1 {d n m : Reg}
    (k : ∀ s', VG.Proof.Sha512.Arm.Only [d] s s' → s'.gpr d = s.gpr n ||| s.gpr m → WP isa (.block rest) s' Q) :
    WP isa (.block (.dp .orr d n (.reg m) :: rest)) s Q :=
  wp_orr (op2_reg _ _) fun s' u => k s' (Only.of_upd u) u.gpr

/-- The registers a region of 64-bit words can be addressed through: every
word `[B + o, B + o + 8)` with `o + 8 ≤ N` is writable. -/
def Reg64 (wr : List Region) (B : BitVec 32) (N : Nat) : Prop :=
  ∀ o, o + 8 ≤ N → InRegions wr (VG.Proof.Sha512.Arm.A B o) 4 ∧ InRegions wr (VG.Proof.Sha512.Arm.A B (o + 4)) 4

theorem wp_ch {f g N : Nat} {B : BitVec 32} {e : BitVec 64} (hN : N ≤ 4096) (hf : f + 8 ≤ N)
    (hg : g + 8 ≤ N) (hR : VG.Proof.Sha512.Arm.Reg64 s.wr B N) (hb : s.gpr .r3 = B) (hp : VG.Proof.Sha512.Arm.Pair s X0 X1 e)
    (k : ∀ s', VG.Proof.Sha512.Arm.Only [Z0, Z1, X0] s s' →
      s'.gpr Z0 = lo (Spec.Sha512.ch e (VG.Proof.Sha512.Arm.rd64 s.mem B f) (VG.Proof.Sha512.Arm.rd64 s.mem B g)) →
      s'.gpr X0 = hi (Spec.Sha512.ch e (VG.Proof.Sha512.Arm.rd64 s.mem B f) (VG.Proof.Sha512.Arm.rd64 s.mem B g)) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (chW f g ++ rest)) s Q := by
  simp only [chW, List.cons_append, List.nil_append]
  simp only [X0, X1, Z0, Z1] at hp k ⊢
  refine VG.Proof.Sha512.Arm.wp_ld1 (B := B) (by omega) hb (hR f hf).1 fun s₁ o₁ v₁ => ?_
  refine VG.Proof.Sha512.Arm.wp_ld1 (B := B) (by omega) (by rw [o₁.gpr _ (by decide), hb]) (by rw [o₁.wr]; exact (hR g hg).1)
    fun s₂ o₂ v₂ => ?_
  refine VG.Proof.Sha512.Arm.wp_eor1 fun s₃ o₃ v₃ => VG.Proof.Sha512.Arm.wp_and1 fun s₄ o₄ v₄ => VG.Proof.Sha512.Arm.wp_eor1 fun s₅ o₅ v₅ => ?_
  have O₅ := (((o₁.trans o₂).trans o₃).trans o₄).trans o₅
  refine VG.Proof.Sha512.Arm.wp_ld1 (B := B) (by omega) (by rw [O₅.gpr _ (by decide), hb]) (by rw [O₅.wr]; exact (hR f hf).2)
    fun s₆ o₆ v₆ => ?_
  refine VG.Proof.Sha512.Arm.wp_ld1 (B := B) (by omega) (by rw [o₆.gpr _ (by decide), O₅.gpr _ (by decide), hb])
    (by rw [o₆.wr, O₅.wr]; exact (hR g hg).2) fun s₇ o₇ v₇ => ?_
  refine VG.Proof.Sha512.Arm.wp_eor1 fun s₈ o₈ v₈ => VG.Proof.Sha512.Arm.wp_and1 fun s₉ o₉ v₉ => VG.Proof.Sha512.Arm.wp_eor1 fun s₁₀ o₁₀ v₁₀ => ?_
  have O := (((((O₅.trans o₆).trans o₇).trans o₈).trans o₉).trans o₁₀)
  refine k s₁₀ (O.mono (by decide)) ?_ ?_
  all_goals
    simp (disch := decide) only [o₁₀.gpr, o₉.gpr, o₈.gpr, o₇.gpr, o₆.gpr, o₅.gpr, o₄.gpr, o₃.gpr,
      o₂.gpr, o₁.gpr, v₁₀, v₉, v₈, v₇, v₆, v₅, v₄, v₃, v₂, v₁, o₆.mem, O₅.mem, o₁.mem, hp.1, hp.2,
      Proof.Sha512.ch_eq, VG.Proof.Sha512.Arm.lo_xor, VG.Proof.Sha512.Arm.lo_and, VG.Proof.Sha512.Arm.hi_xor, VG.Proof.Sha512.Arm.hi_and, VG.Proof.Sha512.Arm.lo_rd64, VG.Proof.Sha512.Arm.hi_rd64]

theorem wp_maj {b c N : Nat} {B : BitVec 32} {a : BitVec 64} (hN : N ≤ 4096) (hb' : b + 8 ≤ N)
    (hc : c + 8 ≤ N) (hR : VG.Proof.Sha512.Arm.Reg64 s.wr B N) (hb : s.gpr .r3 = B) (hp : VG.Proof.Sha512.Arm.Pair s X0 X1 a)
    (k : ∀ s', VG.Proof.Sha512.Arm.Only [Z0, Z1, X0, X1] s s' →
      s'.gpr Z0 = lo (Spec.Sha512.maj a (VG.Proof.Sha512.Arm.rd64 s.mem B b) (VG.Proof.Sha512.Arm.rd64 s.mem B c)) →
      s'.gpr X0 = hi (Spec.Sha512.maj a (VG.Proof.Sha512.Arm.rd64 s.mem B b) (VG.Proof.Sha512.Arm.rd64 s.mem B c)) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (majW b c ++ rest)) s Q := by
  simp only [majW, List.cons_append, List.nil_append]
  simp only [X0, X1, Z0, Z1] at hp k ⊢
  refine VG.Proof.Sha512.Arm.wp_ld1 (B := B) (by omega) hb (hR b hb').1 fun s₁ o₁ v₁ => ?_
  refine VG.Proof.Sha512.Arm.wp_and1 fun s₂ o₂ v₂ => VG.Proof.Sha512.Arm.wp_orr1 fun s₃ o₃ v₃ => ?_
  refine VG.Proof.Sha512.Arm.wp_ld1 (B := B) (by omega) (by simp (disch := decide) only [o₃.gpr, o₂.gpr, o₁.gpr, hb])
    (by simp only [o₃.wr, o₂.wr, o₁.wr]; exact (hR c hc).1) fun s₄ o₄ v₄ => ?_
  refine VG.Proof.Sha512.Arm.wp_and1 fun s₅ o₅ v₅ => VG.Proof.Sha512.Arm.wp_orr1 fun s₆ o₆ v₆ => ?_
  refine VG.Proof.Sha512.Arm.wp_ld1 (B := B) (by omega)
    (by simp (disch := decide) only [o₆.gpr, o₅.gpr, o₄.gpr, o₃.gpr, o₂.gpr, o₁.gpr, hb])
    (by simp only [o₆.wr, o₅.wr, o₄.wr, o₃.wr, o₂.wr, o₁.wr]; exact (hR b hb').2) fun s₇ o₇ v₇ => ?_
  refine VG.Proof.Sha512.Arm.wp_and1 fun s₈ o₈ v₈ => VG.Proof.Sha512.Arm.wp_orr1 fun s₉ o₉ v₉ => ?_
  refine VG.Proof.Sha512.Arm.wp_ld1 (B := B) (by omega)
    (by simp (disch := decide) only [o₉.gpr, o₈.gpr, o₇.gpr, o₆.gpr, o₅.gpr, o₄.gpr, o₃.gpr, o₂.gpr,
      o₁.gpr, hb])
    (by simp only [o₉.wr, o₈.wr, o₇.wr, o₆.wr, o₅.wr, o₄.wr, o₃.wr, o₂.wr, o₁.wr]; exact (hR c hc).2)
    fun s₁₀ o₁₀ v₁₀ => ?_
  refine VG.Proof.Sha512.Arm.wp_and1 fun s₁₁ o₁₁ v₁₁ => VG.Proof.Sha512.Arm.wp_orr1 fun s₁₂ o₁₂ v₁₂ => ?_
  have O := (((((((((((o₁.trans o₂).trans o₃).trans o₄).trans o₅).trans o₆).trans o₇).trans o₈).trans
    o₉).trans o₁₀).trans o₁₁).trans o₁₂)
  refine k s₁₂ (O.mono (by decide)) ?_ ?_
  all_goals
    simp (disch := decide) only [o₁₂.gpr, o₁₁.gpr, o₁₀.gpr, o₉.gpr, o₈.gpr, o₇.gpr, o₆.gpr, o₅.gpr,
      o₄.gpr, o₃.gpr, o₂.gpr, o₁.gpr, v₁₂, v₁₁, v₁₀, v₉, v₈, v₇, v₆, v₅, v₄, v₃, v₂, v₁,
      o₉.mem, o₈.mem, o₇.mem, o₆.mem, o₅.mem, o₄.mem, o₃.mem, o₂.mem, o₁.mem, hp.1, hp.2,
      Proof.Sha512.maj_eq, VG.Proof.Sha512.Arm.lo_or, VG.Proof.Sha512.Arm.lo_and, VG.Proof.Sha512.Arm.hi_or, VG.Proof.Sha512.Arm.hi_and, VG.Proof.Sha512.Arm.lo_rd64, VG.Proof.Sha512.Arm.hi_rd64]

end

/-! ## The message schedule -/

/-- `s'` is `s` with (at most) the registers `ds` changed (and the flags), and memory `m`. -/
structure Wrote (ds : List Reg) (s s' : State) (m : Mem) : Prop where
  gpr : ∀ r, r ∉ ds → s'.gpr r = s.gpr r
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Only.wrote {ds : List Reg} {s₁ s₂ s₃ : State} {m : Mem} (h : VG.Proof.Sha512.Arm.Only ds s₁ s₂) (u : Mupd s₂ s₃ m) :
    VG.Proof.Sha512.Arm.Wrote ds s₁ s₃ m :=
  ⟨fun r hr => by rw [u.gpr, h.gpr r hr], u.mem, u.rd.trans h.rd, u.wr.trans h.wr, u.sp.trans h.sp⟩

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

theorem wp_loadW {i o N : Nat} {Bb B : BitVec 32} (hN : N ≤ 4096) (ho : o + 8 ≤ N) (hio : i + 8 < 4096)
    (hR : VG.Proof.Sha512.Arm.Reg64 s.wr B N) (hb : s.gpr .r3 = B) (hbb : s.gpr .r4 = Bb)
    (hin : InRegions (s.rd ++ s.wr) (VG.Proof.Sha512.Arm.A Bb i) 4) (hin' : InRegions (s.rd ++ s.wr) (VG.Proof.Sha512.Arm.A Bb (i + 4)) 4)
    (k : ∀ s', VG.Proof.Sha512.Arm.Wrote [X0, X1] s s' (VG.Proof.Sha512.Arm.write64 s.mem B o
      (rev (lo (VG.Proof.Sha512.Arm.rd64 s.mem Bb i)) ++ rev (hi (VG.Proof.Sha512.Arm.rd64 s.mem Bb i)))) → WP isa (.block rest) s' Q) :
    WP isa (.block (loadW i o ++ rest)) s Q := by
  have e : loadW i o ++ rest =
      .ldr X0 .r4 i :: .ldr X1 .r4 (i + 4) :: .rev X0 X0 :: .rev X1 X1 :: (VG.Impl.Sha512.Arm.st X1 X0 .r3 o ++ rest) := rfl
  rw [e]
  refine wp_ldr (by omega) (by rw [hbb]) hin fun s₁ u₁ => ?_
  refine wp_ldr (by omega) (by rw [u₁.other _ (by decide), hbb]) (by rw [u₁.rd, u₁.wr]; exact hin')
    fun s₀ u₀ => ?_
  have o₁ : VG.Proof.Sha512.Arm.Only [X0, X1] s s₀ := (Only.of_upd u₁).trans (Only.of_upd u₀)
  have p₁ : VG.Proof.Sha512.Arm.Pair s₀ X0 X1 (VG.Proof.Sha512.Arm.rd64 s.mem Bb i) := by
    refine ⟨?_, ?_⟩
    · rw [u₀.other _ (by decide), u₁.gpr, VG.Proof.Sha512.Arm.lo_rd64]
    · rw [u₀.gpr, u₁.mem, VG.Proof.Sha512.Arm.hi_rd64]
  refine wp_rev fun s₂ u₂ => wp_rev fun s₃ u₃ => ?_
  have O := (o₁.trans (Only.of_upd u₂)).trans (Only.of_upd u₃)
  refine VG.Proof.Sha512.Arm.wp_st (B := B) (x := rev (lo (VG.Proof.Sha512.Arm.rd64 s.mem Bb i)) ++ rev (hi (VG.Proof.Sha512.Arm.rd64 s.mem Bb i))) (by omega)
    (by rw [O.gpr _ (by decide), hb]) ⟨?_, ?_⟩ (by rw [O.wr]; exact (hR o ho).1)
    (by rw [O.wr]; exact (hR o ho).2) fun s₄ u₄ => k s₄ ?_
  · rw [u₃.gpr, u₂.other _ (by decide), p₁.2, VG.Proof.Sha512.Arm.lo_append]
  · rw [u₃.other _ (by decide), u₂.gpr, p₁.1, VG.Proof.Sha512.Arm.hi_append]
  · rw [O.mem] at u₄
    exact (O.mono (by decide)).wrote u₄

theorem wp_expandW {o2 o7 o15 o16 N : Nat} {B : BitVec 32} (hN : N ≤ 4096) (h2 : o2 + 8 ≤ N)
    (h7 : o7 + 8 ≤ N) (h15 : o15 + 8 ≤ N) (h16 : o16 + 8 ≤ N) (hR : VG.Proof.Sha512.Arm.Reg64 s.wr B N)
    (hb : s.gpr .r3 = B)
    (k : ∀ s', VG.Proof.Sha512.Arm.Wrote [X0, X1, Y0, Y1, Z0, Z1] s s' (VG.Proof.Sha512.Arm.write64 s.mem B o16
      (Spec.Sha512.ssig1 (VG.Proof.Sha512.Arm.rd64 s.mem B o2) + VG.Proof.Sha512.Arm.rd64 s.mem B o7 + Spec.Sha512.ssig0 (VG.Proof.Sha512.Arm.rd64 s.mem B o15) +
        VG.Proof.Sha512.Arm.rd64 s.mem B o16)) → WP isa (.block rest) s' Q) :
    WP isa (.block (expandW o2 o7 o15 o16 ++ rest)) s Q := by
  simp only [expandW, List.append_assoc]
  refine VG.Proof.Sha512.Arm.wp_ld (by decide) (by decide) (by omega) hb (hR o2 h2).1 (hR o2 h2).2 fun s₁ o₁ p₁ => ?_
  refine VG.Proof.Sha512.Arm.wp_sig (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) p₁
    fun s₂ o₂ p₂ => ?_
  have O₂ := o₁.trans o₂
  refine VG.Proof.Sha512.Arm.wp_ld (by decide) (by decide) (by omega) (by rw [O₂.gpr _ (by decide), hb])
    (by rw [O₂.wr]; exact (hR o7 h7).1) (by rw [O₂.wr]; exact (hR o7 h7).2) fun s₃ o₃ p₃ => ?_
  refine VG.Proof.Sha512.Arm.wp_add64 (by decide) (by decide) (p₂.of_only o₃ (by decide) (by decide)) p₃
    fun s₄ o₄ p₄ => ?_
  have O₄ := (O₂.trans o₃).trans o₄
  refine VG.Proof.Sha512.Arm.wp_ld (by decide) (by decide) (by omega) (by rw [O₄.gpr _ (by decide), hb])
    (by rw [O₄.wr]; exact (hR o15 h15).1) (by rw [O₄.wr]; exact (hR o15 h15).2) fun s₅ o₅ p₅ => ?_
  refine VG.Proof.Sha512.Arm.wp_sig (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) p₅
    fun s₆ o₆ p₆ => ?_
  refine VG.Proof.Sha512.Arm.wp_add64 (by decide) (by decide) ((p₄.of_only o₅ (by decide) (by decide)).of_only o₆
    (by decide) (by decide)) p₆ fun s₇ o₇ p₇ => ?_
  have O₇ := ((O₄.trans o₅).trans o₆).trans o₇
  refine VG.Proof.Sha512.Arm.wp_ld (by decide) (by decide) (by omega) (by rw [O₇.gpr _ (by decide), hb])
    (by rw [O₇.wr]; exact (hR o16 h16).1) (by rw [O₇.wr]; exact (hR o16 h16).2) fun s₈ o₈ p₈ => ?_
  refine VG.Proof.Sha512.Arm.wp_add64 (by decide) (by decide) (p₇.of_only o₈ (by decide) (by decide)) p₈
    fun s₉ o₉ p₉ => ?_
  have O₉ := (O₇.trans o₈).trans o₉
  refine VG.Proof.Sha512.Arm.wp_st (by omega) (by rw [O₉.gpr _ (by decide), hb]) p₉ (by rw [O₉.wr]; exact (hR o16 h16).1)
    (by rw [O₉.wr]; exact (hR o16 h16).2) fun s₁₀ u₁₀ => k s₁₀ ?_
  rw [O₉.mem] at u₁₀
  have e : ∀ m : Mem, m = s.mem → VG.Proof.Sha512.Arm.evalOps (VG.Proof.Sha512.Arm.rd64 m B o2) ssig1 + VG.Proof.Sha512.Arm.rd64 m B o7 +
      VG.Proof.Sha512.Arm.evalOps (VG.Proof.Sha512.Arm.rd64 m B o15) ssig0 + VG.Proof.Sha512.Arm.rd64 m B o16 = Spec.Sha512.ssig1 (VG.Proof.Sha512.Arm.rd64 s.mem B o2) +
      VG.Proof.Sha512.Arm.rd64 s.mem B o7 + Spec.Sha512.ssig0 (VG.Proof.Sha512.Arm.rd64 s.mem B o15) + VG.Proof.Sha512.Arm.rd64 s.mem B o16 := by
    rintro m rfl; rw [VG.Proof.Sha512.Arm.ssig1_eq, VG.Proof.Sha512.Arm.ssig0_eq]
  rw [O₂.mem, O₄.mem, O₇.mem, e _ rfl] at u₁₀
  exact (O₉.mono (by decide)).wrote u₁₀

end

/-! ## A round -/

/-- `T₁` of a round. -/
def T1 (e f g h k w : BitVec 64) : BitVec 64 :=
  h + Spec.Sha512.bsig1 e + Spec.Sha512.ch e f g + k + w

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

theorem wp_roundW {a b c d e f g h w : Nat} {k : BitVec 64} {B V : BitVec 32}
    (ha : a + 8 ≤ 64) (hb : b + 8 ≤ 64) (hc : c + 8 ≤ 64) (hd : d + 8 ≤ 64) (he : e + 8 ≤ 64)
    (hf : f + 8 ≤ 64) (hg : g + 8 ≤ 64) (hh : h + 8 ≤ 64) (hw : w + 8 ≤ 192)
    (hRB : VG.Proof.Sha512.Arm.Reg64 s.wr B 192) (hRV : VG.Proof.Sha512.Arm.Reg64 s.wr V 64) (h0 : s.gpr .r3 = B) (h3 : s.gpr .r3 = V)
    (K : ∀ s', VG.Proof.Sha512.Arm.Wrote [X0, X1, Y0, Y1, Z0, Z1, E0, E1] s s'
      (VG.Proof.Sha512.Arm.write64 (VG.Proof.Sha512.Arm.write64 s.mem V h
        (VG.Proof.Sha512.Arm.T1 (VG.Proof.Sha512.Arm.rd64 s.mem V e) (VG.Proof.Sha512.Arm.rd64 s.mem V f) (VG.Proof.Sha512.Arm.rd64 s.mem V g) (VG.Proof.Sha512.Arm.rd64 s.mem V h) k (VG.Proof.Sha512.Arm.rd64 s.mem B w) +
          (Spec.Sha512.bsig0 (VG.Proof.Sha512.Arm.rd64 s.mem V a) +
            Spec.Sha512.maj (VG.Proof.Sha512.Arm.rd64 s.mem V a) (VG.Proof.Sha512.Arm.rd64 s.mem V b) (VG.Proof.Sha512.Arm.rd64 s.mem V c))))
        V d (VG.Proof.Sha512.Arm.rd64 s.mem V d +
          VG.Proof.Sha512.Arm.T1 (VG.Proof.Sha512.Arm.rd64 s.mem V e) (VG.Proof.Sha512.Arm.rd64 s.mem V f) (VG.Proof.Sha512.Arm.rd64 s.mem V g) (VG.Proof.Sha512.Arm.rd64 s.mem V h) k (VG.Proof.Sha512.Arm.rd64 s.mem B w))) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (roundW a b c d e f g h k w ++ rest)) s Q := by
  unfold roundW
  simp only [List.append_assoc]
  -- T₁
  refine VG.Proof.Sha512.Arm.wp_ld (by decide) (by decide) (by omega) h3 (hRV h hh).1 (hRV h hh).2 fun s₁ o₁ p₁ => ?_
  refine VG.Proof.Sha512.Arm.wp_ld (by decide) (by decide) (by omega) (by rw [o₁.gpr _ (by decide), h3])
    (by rw [o₁.wr]; exact (hRV e he).1) (by rw [o₁.wr]; exact (hRV e he).2) fun s₂ o₂ p₂ => ?_
  rw [o₁.mem] at p₂
  refine VG.Proof.Sha512.Arm.wp_sig (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) p₂
    fun s₃ o₃ p₃ => ?_
  refine VG.Proof.Sha512.Arm.wp_add64 (by decide) (by decide) ((p₁.of_only o₂ (by decide) (by decide)).of_only o₃
    (by decide) (by decide)) p₃ fun s₄ o₄ p₄ => ?_
  have O₄ := ((o₁.trans o₂).trans o₃).trans o₄
  have p₂' := (p₂.of_only o₃ (by decide) (by decide)).of_only o₄ (by decide) (by decide)
  refine VG.Proof.Sha512.Arm.wp_ch (N := 64) (by omega) hf hg (by rw [O₄.wr]; exact hRV) (by rw [O₄.gpr _ (by decide), h3])
    p₂' fun s₅ o₅ v₅ v₅' => ?_
  rw [O₄.mem] at v₅ v₅'
  refine VG.Proof.Sha512.Arm.wp_add64 (by decide) (by decide) (p₄.of_only o₅ (by decide) (by decide)) ⟨v₅, v₅'⟩
    fun s₆ o₆ p₆ => ?_
  refine VG.Proof.Sha512.Arm.wp_const64 (x := k) (by decide) fun s₇ o₇ p₇ => ?_
  refine VG.Proof.Sha512.Arm.wp_add64 (by decide) (by decide) (p₆.of_only o₇ (by decide) (by decide)) p₇
    fun s₈ o₈ p₈ => ?_
  have O₈ := (((O₄.trans o₅).trans o₆).trans o₇).trans o₈
  refine VG.Proof.Sha512.Arm.wp_ld (by decide) (by decide) (by omega) (by rw [O₈.gpr _ (by decide), h0])
    (by rw [O₈.wr]; exact (hRB w hw).1) (by rw [O₈.wr]; exact (hRB w hw).2) fun s₉ o₉ p₉ => ?_
  rw [O₈.mem] at p₉
  refine VG.Proof.Sha512.Arm.wp_add64 (by decide) (by decide) (p₈.of_only o₉ (by decide) (by decide)) p₉
    fun s₁₀ o₁₀ p₁₀ => ?_
  have O₁₀ := (O₈.trans o₉).trans o₁₀
  -- e' = d + T₁
  refine VG.Proof.Sha512.Arm.wp_ld (by decide) (by decide) (by omega) (by rw [O₁₀.gpr _ (by decide), h3])
    (by rw [O₁₀.wr]; exact (hRV d hd).1) (by rw [O₁₀.wr]; exact (hRV d hd).2) fun s₁₁ o₁₁ p₁₁ => ?_
  rw [O₁₀.mem] at p₁₁
  refine VG.Proof.Sha512.Arm.wp_add64 (by decide) (by decide) p₁₁ (p₁₀.of_only o₁₁ (by decide) (by decide))
    fun s₁₂ o₁₂ p₁₂ => ?_
  have O₁₂ := (O₁₀.trans o₁₁).trans o₁₂
  -- a' = T₁ + Σ₀(a) + Maj(a, b, c)
  refine VG.Proof.Sha512.Arm.wp_ld (by decide) (by decide) (by omega) (by rw [O₁₂.gpr _ (by decide), h3])
    (by rw [O₁₂.wr]; exact (hRV a ha).1) (by rw [O₁₂.wr]; exact (hRV a ha).2) fun s₁₃ o₁₃ p₁₃ => ?_
  rw [O₁₂.mem] at p₁₃
  refine VG.Proof.Sha512.Arm.wp_sig (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) p₁₃
    fun s₁₄ o₁₄ p₁₄ => ?_
  have p₁₀' := ((p₁₀.of_only o₁₁ (by decide) (by decide)).of_only o₁₂ (by decide) (by decide)).of_only
    o₁₃ (by decide) (by decide) |>.of_only o₁₄ (by decide) (by decide)
  refine VG.Proof.Sha512.Arm.wp_add64 (by decide) (by decide) p₁₀' p₁₄ fun s₁₅ o₁₅ p₁₅ => ?_
  have O₁₅ := ((O₁₂.trans o₁₃).trans o₁₄).trans o₁₅
  have p₁₃' := (p₁₃.of_only o₁₄ (by decide) (by decide)).of_only o₁₅ (by decide) (by decide)
  refine VG.Proof.Sha512.Arm.wp_maj (N := 64) (by omega) hb hc (by rw [O₁₅.wr]; exact hRV) (by rw [O₁₅.gpr _ (by decide), h3])
    p₁₃' fun s₁₆ o₁₆ v₁₆ v₁₆' => ?_
  rw [O₁₅.mem] at v₁₆ v₁₆'
  refine VG.Proof.Sha512.Arm.wp_add64 (by decide) (by decide) (p₁₅.of_only o₁₆ (by decide) (by decide)) ⟨v₁₆, v₁₆'⟩
    fun s₁₇ o₁₇ p₁₇ => ?_
  have O₁₇ := (O₁₅.trans o₁₆).trans o₁₇
  have p₁₂' := (((((p₁₂.of_only o₁₃ (by decide) (by decide)).of_only o₁₄ (by decide) (by decide)).of_only
    o₁₅ (by decide) (by decide)).of_only o₁₆ (by decide) (by decide)).of_only o₁₇ (by decide) (by decide))
  -- Store them.
  refine VG.Proof.Sha512.Arm.wp_st (by omega) (by rw [O₁₇.gpr _ (by decide), h3]) p₁₇ (by rw [O₁₇.wr]; exact (hRV h hh).1)
    (by rw [O₁₇.wr]; exact (hRV h hh).2) fun s₁₈ u₁₈ => ?_
  refine VG.Proof.Sha512.Arm.wp_st (by omega) (by rw [u₁₈.gpr, O₁₇.gpr _ (by decide), h3])
    ⟨by rw [u₁₈.gpr]; exact p₁₂'.1, by rw [u₁₈.gpr]; exact p₁₂'.2⟩
    (by rw [u₁₈.wr, O₁₇.wr]; exact (hRV d hd).1) (by rw [u₁₈.wr, O₁₇.wr]; exact (hRV d hd).2)
    fun s₁₉ u₁₉ => K s₁₉ ⟨fun r hr => ?_, ?_, by rw [u₁₉.rd, u₁₈.rd, O₁₇.rd],
      by rw [u₁₉.wr, u₁₈.wr, O₁₇.wr], by rw [u₁₉.sp, u₁₈.sp, O₁₇.sp]⟩
  · rw [u₁₉.gpr, u₁₈.gpr]
    exact (O₁₇.mono (by decide)).gpr r hr
  · rw [u₁₉.mem, u₁₈.mem, O₁₇.mem]
    simp only [VG.Proof.Sha512.Arm.T1, VG.Proof.Sha512.Arm.bsig1_eq, VG.Proof.Sha512.Arm.bsig0_eq, BitVec.add_assoc]

end

end VG.Proof.Sha512.Arm

/-!
# SHA-512 on ARMv7: the message schedule and the rounds
-/

namespace VG.Proof.Sha512.Arm

open VG VG.Arm VG.Impl.Sha512.Arm
open VG.Spec.Sha512 (HashValue Word Block W)
open VG.Proof.MdStream.Arm (contains_offset readW_writeW_save)

/-! ## 64-bit words in memory -/

theorem A_eq {b : BitVec 32} {off : Nat} (h : b.toNat + off < 2 ^ 32) :
    VG.Proof.Sha512.Arm.A b off = State.addr b + BitVec.ofNat 64 off :=
  addr_add h

theorem rd64_write64_self (m : Mem) {b : BitVec 32} {o : Nat} (x : BitVec 64)
    (h : b.toNat + o + 8 ≤ 2 ^ 32) : VG.Proof.Sha512.Arm.rd64 (VG.Proof.Sha512.Arm.write64 m b o x) b o = x := by
  simp only [VG.Proof.Sha512.Arm.rd64, VG.Proof.Sha512.Arm.write64]
  rw [Mem.readW_writeW_self32, VG.Proof.Sha512.Arm.A_eq (by omega), VG.Proof.Sha512.Arm.A_eq (b := b) (off := o + 4) (by omega),
    readW_writeW_save _ _ _ (by omega) (by omega) (by omega), Mem.readW_writeW_self32, VG.Proof.Sha512.Arm.hi_append_lo]

theorem rd64_write64_ne (m : Mem) {b : BitVec 32} {o o' : Nat} (x : BitVec 64)
    (h : b.toNat + o + 8 ≤ 2 ^ 32) (h' : b.toNat + o' + 8 ≤ 2 ^ 32) (hs : o + 8 ≤ o' ∨ o' + 8 ≤ o) :
    VG.Proof.Sha512.Arm.rd64 (VG.Proof.Sha512.Arm.write64 m b o x) b o' = VG.Proof.Sha512.Arm.rd64 m b o' := by
  simp only [VG.Proof.Sha512.Arm.rd64, VG.Proof.Sha512.Arm.write64]
  rw [VG.Proof.Sha512.Arm.A_eq (b := b) (off := o) (by omega), VG.Proof.Sha512.Arm.A_eq (b := b) (off := o + 4) (by omega),
    VG.Proof.Sha512.Arm.A_eq (b := b) (off := o') (by omega), VG.Proof.Sha512.Arm.A_eq (b := b) (off := o' + 4) (by omega),
    readW_writeW_save _ _ _ (by omega) (by omega) (by omega),
    readW_writeW_save _ _ _ (by omega) (by omega) (by omega),
    readW_writeW_save _ _ _ (by omega) (by omega) (by omega),
    readW_writeW_save _ _ _ (by omega) (by omega) (by omega)]

theorem contains_A {b : BitVec 32} {N o : Nat} (hfit : b.toNat + N ≤ 2 ^ 32) (ho : o + 4 ≤ N) :
    (⟨State.addr b, N⟩ : Region).Contains (VG.Proof.Sha512.Arm.A b o) 4 := by
  rw [VG.Proof.Sha512.Arm.A_eq (by omega)]; exact contains_offset ho (by omega)

theorem rd64_write64_disj (m : Mem) {b b' : BitVec 32} {N N' o o' : Nat} (x : BitVec 64)
    (hd : Region.Disjoint ⟨State.addr b, N⟩ ⟨State.addr b', N'⟩)
    (hfit : b.toNat + N ≤ 2 ^ 32) (hfit' : b'.toNat + N' ≤ 2 ^ 32) (ho : o + 8 ≤ N) (ho' : o' + 8 ≤ N') :
    VG.Proof.Sha512.Arm.rd64 (VG.Proof.Sha512.Arm.write64 m b o x) b' o' = VG.Proof.Sha512.Arm.rd64 m b' o' := by
  have s : ∀ i j, i + 4 ≤ N → j + 4 ≤ N' → Mem.Sep (VG.Proof.Sha512.Arm.A b' j) (32 / 8) (VG.Proof.Sha512.Arm.A b i) (32 / 8) :=
    fun i j hi hj => hd.symm.sep (VG.Proof.Sha512.Arm.contains_A hfit' hj) (VG.Proof.Sha512.Arm.contains_A hfit hi)
  simp only [VG.Proof.Sha512.Arm.rd64, VG.Proof.Sha512.Arm.write64]
  rw [Mem.readW_writeW_sep (s _ _ (by omega) (by omega)) (by decide),
    Mem.readW_writeW_sep (s _ _ (by omega) (by omega)) (by decide),
    Mem.readW_writeW_sep (s _ _ (by omega) (by omega)) (by decide),
    Mem.readW_writeW_sep (s _ _ (by omega) (by omega)) (by decide)]

theorem frame_write64 {rs : List Region} {m m' : Mem} (h : Frame rs m m') {b : BitVec 32} {N o : Nat}
    (hr : ⟨State.addr b, N⟩ ∈ rs) (hfit : b.toNat + N ≤ 2 ^ 32) (ho : o + 8 ≤ N) (x : BitVec 64) :
    Frame rs m (VG.Proof.Sha512.Arm.write64 m' b o x) :=
  (h.writeW hr _ (VG.Proof.Sha512.Arm.contains_A hfit (by omega))).writeW hr _ (VG.Proof.Sha512.Arm.contains_A hfit (by omega))

theorem Reg64.of_mem {wr : List Region} {B : BitVec 32} {N : Nat} (h : ⟨State.addr B, N⟩ ∈ wr)
    (hfit : B.toNat + N ≤ 2 ^ 32) : VG.Proof.Sha512.Arm.Reg64 wr B N :=
  fun _ ho => ⟨⟨_, h, VG.Proof.Sha512.Arm.contains_A hfit (by omega)⟩, ⟨_, h, VG.Proof.Sha512.Arm.contains_A hfit (by omega)⟩⟩

theorem rd64_frame {rs : List Region} {m m' : Mem} (h : Frame rs m m') {b : BitVec 32} {N o : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨State.addr b, N⟩ r) (hfit : b.toNat + N ≤ 2 ^ 32) (ho : o + 8 ≤ N) :
    VG.Proof.Sha512.Arm.rd64 m' b o = VG.Proof.Sha512.Arm.rd64 m b o := by
  simp only [VG.Proof.Sha512.Arm.rd64]
  rw [h.readW (VG.Proof.Sha512.Arm.contains_A hfit (by omega)) hd (by decide),
    h.readW (VG.Proof.Sha512.Arm.contains_A hfit (by omega)) hd (by decide)]

/-! ## Offsets -/

theorem vOff_lt (t k : Nat) : vOff t k + 8 ≤ 64 := by simp only [vOff]; omega

theorem wOff_lt (j : Nat) : wOff j + 8 ≤ 192 := by simp only [wOff]; omega

theorem vOff_lt' (t k : Nat) : vOff t k + 8 ≤ 224 := by simp only [vOff]; omega

theorem wOff_lt' (j : Nat) : wOff j + 8 ≤ 224 := by simp only [wOff]; omega

/-- The working variables are below the message schedule. -/
theorem vw_sep (t k j : Nat) : vOff t k + 8 ≤ wOff j := by simp only [vOff, wOff]; omega

theorem vOff_sep (t : Nat) {i j : Nat} (hi : i < 8) (hj : j < 8) (h : i ≠ j) :
    vOff t i + 8 ≤ vOff t j ∨ vOff t j + 8 ≤ vOff t i := by
  simp only [vOff]; omega

theorem vOff_succ_zero (t : Nat) : vOff (t + 1) 0 = vOff t 7 := by simp only [vOff]; omega

theorem vOff_succ (t k : Nat) (hk : k < 7) : vOff (t + 1) (k + 1) = vOff t k := by
  simp only [vOff]; omega

theorem wOff_sep {i j : Nat} (h : i % 16 ≠ j % 16) : wOff i + 8 ≤ wOff j ∨ wOff j + 8 ≤ wOff i := by
  simp only [wOff]; omega

/-! ## Rounds -/

/-- The registers the rounds write. -/
def temps : List Reg := [X0, X1, Y0, Y1, Z0, Z1, E0, E1]

/-- The hash value's region and the scratch region (the working variables,
the message schedule and the saved registers). -/
abbrev stR (st : BitVec 32) : Region := ⟨State.addr st, 64⟩
abbrev scrR (scr : BitVec 32) : Region := ⟨State.addr scr, 224⟩
/-- The part of the scratch region the rounds write (not the saved registers). -/
abbrev workR (scr : BitVec 32) : Region := ⟨State.addr scr, 192⟩

/-- What the rounds need of their state `s`, with `state = st`, `scratch = scr`. -/
structure Ctx (st scr : BitVec 32) (s : State) : Prop where
  r0 : s.gpr .r0 = st
  r3 : s.gpr .r3 = scr
  fitS : st.toNat + 64 ≤ 2 ^ 32
  fitV : scr.toNat + 224 ≤ 2 ^ 32
  disj : (VG.Proof.Sha512.Arm.stR st).Disjoint (VG.Proof.Sha512.Arm.scrR scr)
  wS : VG.Proof.Sha512.Arm.Reg64 s.wr st 64
  wV : VG.Proof.Sha512.Arm.Reg64 s.wr scr 224

theorem Wrote.mono' {ds es : List Reg} {s s' : State} {m : Mem} (w : VG.Proof.Sha512.Arm.Wrote ds s s' m)
    (h : ∀ r ∈ ds, r ∈ es) : VG.Proof.Sha512.Arm.Wrote es s s' m :=
  ⟨fun r hr => w.gpr r fun hd => hr (h r hd), w.mem, w.rd, w.wr, w.sp⟩

theorem Ctx.of_eq {st scr : BitVec 32} {s s' : State} (c : VG.Proof.Sha512.Arm.Ctx st scr s) (h0 : s'.gpr .r0 = s.gpr .r0)
    (h3 : s'.gpr .r3 = s.gpr .r3) (hwr : s'.wr = s.wr) : VG.Proof.Sha512.Arm.Ctx st scr s' :=
  ⟨h0.trans c.r0, h3.trans c.r3, c.fitS, c.fitV, c.disj, hwr ▸ c.wS, hwr ▸ c.wV⟩

theorem Ctx.of_wrote {st scr : BitVec 32} {s s' : State} {ds : List Reg} {m : Mem} (c : VG.Proof.Sha512.Arm.Ctx st scr s)
    (w : VG.Proof.Sha512.Arm.Wrote ds s s' m) (h0 : .r0 ∉ ds) (h3 : .r3 ∉ ds) : VG.Proof.Sha512.Arm.Ctx st scr s' :=
  ⟨(w.gpr _ h0).trans c.r0, (w.gpr _ h3).trans c.r3, c.fitS, c.fitV, c.disj, w.wr ▸ c.wS,
    w.wr ▸ c.wV⟩

/-- The rounds' invariant after `t` rounds, from `s₀`. -/
structure RInv (st scr : BitVec 32) (H : HashValue) (M : Block) (s₀ : State) (t : Nat) (s : State) :
    Prop where
  vars : ∀ k (hk : k < 8), VG.Proof.Sha512.Arm.rd64 s.mem scr (vOff t k) = (Spec.Sha512.rounds H M t)[k]
  win : ∀ j < t, t ≤ j + 16 → VG.Proof.Sha512.Arm.rd64 s.mem scr (wOff j) = W M j
  hash : ∀ k < 8, VG.Proof.Sha512.Arm.rd64 s.mem st (8 * k) = VG.Proof.Sha512.Arm.rd64 s₀.mem st (8 * k)
  gpr : ∀ r, r ∉ VG.Proof.Sha512.Arm.temps → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [VG.Proof.Sha512.Arm.workR scr] s₀.mem s.mem

theorem roundKW_get (v : HashValue) (a b : Word) {k : Nat} (hk : k < 8) (h0 : k ≠ 0) (h4 : k ≠ 4) :
    (roundKW v a b)[k] = v[k - 1] := by
  rcases (by omega : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The memory after round `t`'s message word and round. -/
theorem round_ok {st scr : BitVec 32} {H : HashValue} {M : Block} {s₀ s : State} {t : Nat}
    (c : VG.Proof.Sha512.Arm.Ctx st scr s) (hI : VG.Proof.Sha512.Arm.RInv st scr H M s₀ t s) (ht : t < 80) (s₁ : State)
    (w₁ : VG.Proof.Sha512.Arm.Wrote VG.Proof.Sha512.Arm.temps s s₁ (VG.Proof.Sha512.Arm.write64 s.mem scr (wOff t) (W M t))) :
    WP isa (.block (round t)) s₁ (VG.Proof.Sha512.Arm.RInv st scr H M s₀ (t + 1)) := by
  have c₁ := c.of_wrote w₁ (by decide) (by decide)
  have fitV := c.fitV
  have fitS := c.fitS
  set v := Spec.Sha512.rounds H M t with hv
  have hvar : ∀ k (hk : k < 8), VG.Proof.Sha512.Arm.rd64 s₁.mem scr (vOff t k) = v[k] := fun k hk => by
    rw [w₁.mem, VG.Proof.Sha512.Arm.rd64_write64_ne _ _ (by have := VG.Proof.Sha512.Arm.wOff_lt' t; omega) (by have := VG.Proof.Sha512.Arm.vOff_lt' t k; omega)
      (.inr (VG.Proof.Sha512.Arm.vw_sep t k t)), hI.vars k hk]
  have hw : VG.Proof.Sha512.Arm.rd64 s₁.mem scr (wOff t) = W M t := by
    rw [w₁.mem, VG.Proof.Sha512.Arm.rd64_write64_self _ _ (by have := VG.Proof.Sha512.Arm.wOff_lt' t; omega)]
  rw [← List.append_nil (round t)]
  unfold round
  refine VG.Proof.Sha512.Arm.wp_roundW (VG.Proof.Sha512.Arm.vOff_lt t 0) (VG.Proof.Sha512.Arm.vOff_lt t 1) (VG.Proof.Sha512.Arm.vOff_lt t 2) (VG.Proof.Sha512.Arm.vOff_lt t 3) (VG.Proof.Sha512.Arm.vOff_lt t 4) (VG.Proof.Sha512.Arm.vOff_lt t 5)
    (VG.Proof.Sha512.Arm.vOff_lt t 6) (VG.Proof.Sha512.Arm.vOff_lt t 7) (VG.Proof.Sha512.Arm.wOff_lt t) (fun o ho => c₁.wV o (by omega))
    (fun o ho => c₁.wV o (by omega)) c₁.r3 c₁.r3 fun s₂ w₂ => WP.block_nil ?_
  rw [hvar 0 (by omega), hvar 1 (by omega), hvar 2 (by omega), hvar 3 (by omega), hvar 4 (by omega),
    hvar 5 (by omega), hvar 6 (by omega), hvar 7 (by omega), hw] at w₂
  have hnext : Spec.Sha512.rounds H M (t + 1) = roundKW v (Spec.Sha512.K t) (W M t) := by
    rw [rounds_succ, round_eq]
  have v3 := VG.Proof.Sha512.Arm.vOff_lt' t 3
  have v7 := VG.Proof.Sha512.Arm.vOff_lt' t 7
  refine ⟨fun k hk => ?_, fun j hj hj' => ?_, fun k hk => ?_, fun r hr => ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [w₂.mem, hnext]
    by_cases h4 : k = 4
    · subst h4
      rw [show vOff (t + 1) 4 = vOff t 3 from VG.Proof.Sha512.Arm.vOff_succ t 3 (by omega),
        VG.Proof.Sha512.Arm.rd64_write64_self (b := scr) (o := vOff t 3) _ _ (by omega)]
      rfl
    · have e3 : ∀ i, i < 8 → i ≠ 3 → vOff t i + 8 ≤ vOff t 3 ∨ vOff t 3 + 8 ≤ vOff t i :=
        fun i hi h => VG.Proof.Sha512.Arm.vOff_sep t hi (by omega) h
      by_cases h0 : k = 0
      · subst h0
        rw [VG.Proof.Sha512.Arm.vOff_succ_zero, VG.Proof.Sha512.Arm.rd64_write64_ne (b := scr) (o := vOff t 3) (o' := vOff t 7) _ _
          (by omega) (by omega) (e3 7 (by omega) (by omega)).symm,
          VG.Proof.Sha512.Arm.rd64_write64_self (b := scr) (o := vOff t 7) _ _ (by omega)]
        rfl
      · obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
        rw [VG.Proof.Sha512.Arm.vOff_succ t i (by omega), VG.Proof.Sha512.Arm.rd64_write64_ne (b := scr) (o := vOff t 3) (o' := vOff t i) _ _
          (by omega) (by have := VG.Proof.Sha512.Arm.vOff_lt' t i; omega) (e3 i (by omega) (by omega)).symm,
          VG.Proof.Sha512.Arm.rd64_write64_ne (b := scr) (o := vOff t 7) (o' := vOff t i) _ _
            (by omega) (by have := VG.Proof.Sha512.Arm.vOff_lt' t i; omega)
            (VG.Proof.Sha512.Arm.vOff_sep t (by omega) (by omega) (by omega)),
          hvar i (by omega), VG.Proof.Sha512.Arm.roundKW_get _ _ _ hk h0 h4]
        simp only [Nat.add_sub_cancel]
  · have wj := VG.Proof.Sha512.Arm.wOff_lt' j
    rw [w₂.mem, VG.Proof.Sha512.Arm.rd64_write64_ne (b := scr) (o := vOff t 3) (o' := wOff j) _ _ (by omega) (by omega)
        (.inl (VG.Proof.Sha512.Arm.vw_sep t 3 j)),
      VG.Proof.Sha512.Arm.rd64_write64_ne (b := scr) (o := vOff t 7) (o' := wOff j) _ _ (by omega) (by omega)
        (.inl (VG.Proof.Sha512.Arm.vw_sep t 7 j))]
    by_cases hjt : j = t
    · subst hjt; exact hw
    · rw [w₁.mem, VG.Proof.Sha512.Arm.rd64_write64_ne (b := scr) (o := wOff t) (o' := wOff j) _ _
        (by have := VG.Proof.Sha512.Arm.wOff_lt' t; omega) (by omega) (VG.Proof.Sha512.Arm.wOff_sep (by omega))]
      exact hI.win j (by omega) (by omega)
  · rw [w₂.mem, VG.Proof.Sha512.Arm.rd64_write64_disj _ _ c.disj.symm fitV fitS (VG.Proof.Sha512.Arm.vOff_lt' t 3) (by omega : 8 * k + 8 ≤ 64),
      VG.Proof.Sha512.Arm.rd64_write64_disj _ _ c.disj.symm fitV fitS (VG.Proof.Sha512.Arm.vOff_lt' t 7) (by omega : 8 * k + 8 ≤ 64), w₁.mem,
      VG.Proof.Sha512.Arm.rd64_write64_disj _ _ c.disj.symm fitV fitS (VG.Proof.Sha512.Arm.wOff_lt' t) (by omega : 8 * k + 8 ≤ 64)]
    exact hI.hash k hk
  · rw [w₂.gpr r hr, w₁.gpr r hr, hI.gpr r hr]
  · rw [w₂.rd, w₁.rd, hI.rd]
  · rw [w₂.wr, w₁.wr, hI.wr]
  · rw [w₂.sp, w₁.sp, hI.sp]
  · rw [w₂.mem, w₁.mem]
    have w := VG.Proof.Sha512.Arm.wOff_lt t
    have v3 := VG.Proof.Sha512.Arm.vOff_lt t 3
    have v7 := VG.Proof.Sha512.Arm.vOff_lt t 7
    exact VG.Proof.Sha512.Arm.frame_write64 (N := 192) (VG.Proof.Sha512.Arm.frame_write64 (N := 192) (VG.Proof.Sha512.Arm.frame_write64 (N := 192) hI.frame (by simp)
      (by omega) (VG.Proof.Sha512.Arm.wOff_lt t) _) (by simp) (by omega) (by omega) _) (by simp) (by omega) (by omega) _

theorem Ctx.of_rinv {st scr : BitVec 32} {H : HashValue} {M : Block} {s₀ s : State} {t : Nat}
    (c : VG.Proof.Sha512.Arm.Ctx st scr s₀) (hI : VG.Proof.Sha512.Arm.RInv st scr H M s₀ t s) : VG.Proof.Sha512.Arm.Ctx st scr s :=
  ⟨(hI.gpr _ (by decide)).trans c.r0, (hI.gpr _ (by decide)).trans c.r3, c.fitS, c.fitV, c.disj,
    hI.wr ▸ c.wS, hI.wr ▸ c.wV⟩

/-- The block at `bk`'s words, as `loadW` makes them from its bytes. -/
def Raw (bk : BitVec 32) (M : Block) (m : Mem) : Prop :=
  ∀ j < 16, rev (lo (VG.Proof.Sha512.Arm.rd64 m bk (8 * j))) ++ rev (hi (VG.Proof.Sha512.Arm.rd64 m bk (8 * j))) = W M j

/-- Where the block is: at `bk` (in `r4`), readable, and apart from the scratch region. -/
structure BlkCtx (scr bk : BitVec 32) (s₀ : State) : Prop where
  r4 : s₀.gpr .r4 = bk
  fitB : bk.toNat + 128 ≤ 2 ^ 32
  disj : Region.Disjoint ⟨State.addr bk, 128⟩ (VG.Proof.Sha512.Arm.workR scr)
  rd : ∀ o, o + 4 ≤ 128 → InRegions (s₀.rd ++ s₀.wr) (VG.Proof.Sha512.Arm.A bk o) 4

theorem step_ok {st scr bk : BitVec 32} {H : HashValue} {M : Block} {s₀ s : State} {t : Nat}
    (c₀ : VG.Proof.Sha512.Arm.Ctx st scr s₀) (hB : VG.Proof.Sha512.Arm.BlkCtx scr bk s₀) (hM : VG.Proof.Sha512.Arm.Raw bk M s₀.mem)
    (hI : VG.Proof.Sha512.Arm.RInv st scr H M s₀ t s) (ht : t < 80) :
    WP isa (.block (schedule t ++ round t)) s (VG.Proof.Sha512.Arm.RInv st scr H M s₀ (t + 1)) := by
  have c := c₀.of_rinv hI
  by_cases h16 : t < 16
  · unfold schedule; simp only [h16, ↓reduceIte]
    refine VG.Proof.Sha512.Arm.wp_loadW (N := 224) (by omega) (VG.Proof.Sha512.Arm.wOff_lt' t) (by omega) c.wV c.r3
      (by rw [hI.gpr _ (by decide), hB.r4]) (by rw [hI.rd, hI.wr]; exact hB.rd _ (by omega))
      (by rw [hI.rd, hI.wr]; exact hB.rd _ (by omega)) fun s₁ w₁ => VG.Proof.Sha512.Arm.round_ok c hI ht s₁ ?_
    rw [VG.Proof.Sha512.Arm.rd64_frame hI.frame (fun r hr => by simp at hr; subst hr; exact hB.disj) hB.fitB (by omega),
      hM t h16] at w₁
    exact (w₁.mono' (by decide))
  · unfold schedule; simp only [h16, ↓reduceIte]
    have e : ∀ i, 1 ≤ i → i ≤ 16 → VG.Proof.Sha512.Arm.rd64 s.mem scr (wOff (t + 16 - i)) = W M (t - i) :=
      fun i hi hi' => by
        rw [show wOff (t + 16 - i) = wOff (t - i) by simp only [wOff]; omega]
        exact hI.win _ (by omega) (by omega)
    refine VG.Proof.Sha512.Arm.wp_expandW (N := 224) (by omega) (VG.Proof.Sha512.Arm.wOff_lt' _) (VG.Proof.Sha512.Arm.wOff_lt' _) (VG.Proof.Sha512.Arm.wOff_lt' _) (VG.Proof.Sha512.Arm.wOff_lt' _) c.wV
      c.r3 fun s₁ w₁ => VG.Proof.Sha512.Arm.round_ok c hI ht s₁ ?_
    have e16 : VG.Proof.Sha512.Arm.rd64 s.mem scr (wOff t) = W M (t - 16) := by
      rw [← e 16 (by omega) (by omega), show t + 16 - 16 = t by omega]
    rw [show t + 14 = t + 16 - 2 by omega, show t + 9 = t + 16 - 7 by omega,
      show t + 1 = t + 16 - 15 by omega, e 2 (by omega) (by omega), e 7 (by omega) (by omega),
      e 15 (by omega) (by omega), e16, ← W_ge M (by omega)] at w₁
    exact (w₁.mono' (by decide))

theorem rounds_ok {st scr bk : BitVec 32} {H : HashValue} {M : Block} {s₀ : State}
    (c₀ : VG.Proof.Sha512.Arm.Ctx st scr s₀) (hB : VG.Proof.Sha512.Arm.BlkCtx scr bk s₀) (hM : VG.Proof.Sha512.Arm.Raw bk M s₀.mem)
    (h0 : ∀ k (hk : k < 8), VG.Proof.Sha512.Arm.rd64 s₀.mem scr (8 * k) = H[k]) :
    ∀ t ≤ 80, WP isa (rounds t) s₀ (VG.Proof.Sha512.Arm.RInv st scr H M s₀ t) := by
  intro t ht
  induction t with
  | zero =>
    refine WP.block_nil ⟨fun k hk => ?_, fun j hj => absurd hj (by omega),
      fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
    rw [show vOff 0 k = 8 * k by simp only [vOff]; omega, h0 k hk]; rfl
  | succ t ih =>
    exact WP.seq (WP.mono (ih (by omega)) fun s hI => VG.Proof.Sha512.Arm.step_ok c₀ hB hM hI (by omega))

end VG.Proof.Sha512.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha512.Arm.Lit`. -/
section

/-!
# SHA-512 on Arm: the code as literals
-/

namespace VG

materialize_code Impl.Sha512.Arm.compress
materialize_code Impl.Sha512.Arm.Stream.update
materialize_code Impl.Sha512.Arm.Stream.finalize

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha512.Arm.Compress`. -/
section

/-!
# SHA-512 compression function on ARMv7: the whole function
-/

/-!
## SHA-512: the 32-bit ARM contracts

The contracts the proofs are written against; the artifacts are emitted with
the shared contracts of `Spec/`, which imply these (`Contract.Implies`). The
contracts of the 32-bit ARM implementations of the compression function and of
the streaming functions (`init`, `update`, `finalize`; see
`VG.Spec.Sha512.Repr`), in terms of `Spec/Sha512.lean`, with the arguments
where AAPCS passes them.
-/

namespace VG.Proof.Sha512

open Spec.Sha512

open VG.Arm in
/-- 32-bit ARM contract for
`vg_sha512_compress(state: *mut [u64; 8], blocks: *const [u8; 128], n: usize, scratch: *mut [u64; 28])`:
updates the hash value at `state` with the `n` 128-byte blocks at `blocks`.

The code may read `blocks` (`128 * n` bytes) and read and write `state`
(64 bytes) and `scratch` (224 bytes, whose contents on exit are unspecified).
These may not overlap each other, and none of them may wrap around the end of
the (32-bit) address space. The pointers and `n` are public; the hash value
and the blocks are secret. -/
def compressArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 64⟩
    let blocks : Region := ⟨State.addr (s.gpr .r1), 128 * (s.gpr .r2).toNat⟩
    let scratch : Region := ⟨State.addr (s.gpr .r3), 224⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
    (s.gpr .r0).toNat + 64 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 128 * (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
    (s.gpr .r3).toNat + 224 ≤ 2 ^ 32
  post s s' :=
    stateAt s'.mem (State.addr (s.gpr .r0)) =
      compressBlocks (stateAt s.mem (State.addr (s.gpr .r0))) s.mem (State.addr (s.gpr .r1))
        (s.gpr .r2).toNat
  pub s₁ s₂ :=
    s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3

open VG.Arm in
/-- The 64-bit `count` argument of `update`/`finalize`, in `r2:r3` (AAPCS: the
low word in `r2`). -/
def countArm (s : Arm.State) : BitVec 64 := s.gpr .r3 ++ s.gpr .r2

open VG.Arm in
/-- 32-bit ARM contract for `vg_<alg>_init(state: *mut [u8; 192])`, where `iv`
is the initial hash value of `<alg>`: makes the streaming state at `state`
represent the empty message, hashed from `iv`.

The code may write `state` (192 bytes), which may not wrap around the end of
the (32-bit) address space. The pointer is public. -/
def initArm (iv : HashValue) : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 192⟩
    s.rd = [] ∧ s.wr = [state] ∧ (s.gpr .r0).toNat + 192 ≤ 2 ^ 32
  post s s' := Repr iv s'.mem (State.addr (s.gpr .r0)) []
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0

open VG.Arm in
/-- 32-bit ARM contract for
`vg_sha512_update(state: *mut [u8; 192], count: u64, data: *const u8, len: usize, scratch: *mut [u64; 34])`:
if the streaming state at `state` represents a message `m` of `count` bytes
(modulo 2⁶⁴), hashed from any initial hash value, then afterwards it
represents `m` followed by the `len` bytes at `data`, from the same one.

Under AAPCS, `state` is in `r0`, `count` in `r2:r3`, and `data`, `len` and
`scratch` are the stack arguments 0, 1 and 2. The code may read those
arguments (12 bytes at `sp`) and `data` (`len` bytes), and read and write
`state` (192 bytes) and `scratch` (272 bytes, whose contents on exit are
unspecified). The writable buffers may not overlap each other, the data or
the arguments; the data may not overlap them either; and nothing may wrap
around the end of the (32-bit) address space. `sp`, the pointers, `count`
and `len` are public; the state and the data are secret. -/
def updateArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 192⟩
    let data : Region := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 2), 272⟩
    let args : Region := ⟨stackArgAddr s 0, 12⟩
    s.rd = [data, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + 192 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32 ∧
    (stackArg s 2).toNat + 272 ≤ 2 ^ 32 ∧ s.sp.toNat + 12 ≤ 2 ^ 32
  post s s' := ∀ iv m, Repr iv s.mem (State.addr (s.gpr .r0)) m → VG.Proof.Sha512.countArm s = BitVec.ofNat 64 m.length →
    Repr iv s'.mem (State.addr (s.gpr .r0))
      (m ++ bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2

open VG.Arm in
/-- 32-bit ARM contract for
`vg_sha512_finalize(state: *mut [u8; 192], count: u64, out: *mut [u8; 64], scratch: *mut [u64; 34])`:
if the streaming state at `state` represents a message `m` of `count` bytes,
fewer than 2⁶⁴, hashed from the initial hash value `iv`, writes the final
hash value `H⁽ᴺ⁾` of `m` from `iv` (64 bytes; `finalHash iv m`) to `out`.

Under AAPCS, `state` is in `r0`, `count` in `r2:r3`, and `out` and `scratch`
are the stack arguments 0 and 1. The code may read those arguments (8 bytes
at `sp`), and read and write `state` (192 bytes, whose contents on exit are
unspecified), `out` (64 bytes) and `scratch` (272 bytes, whose contents on
exit are unspecified). These may not overlap each other or the arguments,
and nothing may wrap around the end of the (32-bit) address space. `sp`, the
pointers and `count` are public; the state is secret. -/
def finalizeArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 192⟩
    let out : Region := ⟨State.addr (stackArg s 0), 64⟩
    let scratch : Region := ⟨State.addr (stackArg s 1), 272⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + 192 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 64 ≤ 2 ^ 32 ∧
    (stackArg s 1).toNat + 272 ≤ 2 ^ 32 ∧ s.sp.toNat + 8 ≤ 2 ^ 32
  post s s' := ∀ iv m, Repr iv s.mem (State.addr (s.gpr .r0)) m → m.length < 2 ^ 64 →
    VG.Proof.Sha512.countArm s = BitVec.ofNat 64 m.length →
    bytesAt s'.mem (State.addr (stackArg s 0)) 64 = finalHash iv m
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

end VG.Proof.Sha512


namespace VG.Proof.Sha512.Arm

open VG VG.Arm VG.Impl.Sha512.Arm
open VG.Spec.Sha512 (HashValue Word Block W stateAt blockAt compress compressBlocks parseBlock)
open VG.Proof.MdStream.Arm (contains_offset)
open VG.Proof.MdStream.Arm (sub_offset wp_add wp_subs wp_mov wp_cmp op2_imm op2_reg eval_ne)

/-! ## Memory -/

theorem stateAt_get {st : BitVec 32} (hfit : st.toNat + 64 ≤ 2 ^ 32) (m : Mem) {k : Nat} (hk : k < 8) :
    (stateAt m (State.addr st))[k] = VG.Proof.Sha512.Arm.rd64 m st (8 * k) := by
  simp only [stateAt, Vector.getElem_ofFn, VG.Proof.Sha512.Arm.rd64]
  rw [VG.Proof.Sha512.Arm.readW64, VG.Proof.Sha512.Arm.A_eq (by omega), VG.Proof.Sha512.Arm.A_eq (by omega),
    show State.addr st + BitVec.ofNat 64 (8 * k) + 4 = State.addr st + BitVec.ofNat 64 (8 * k + 4) from
      Offset.add_ofNat_add_ofNat _ _ 4]

theorem stateAt_ext {st : BitVec 32} (hfit : st.toNat + 64 ≤ 2 ^ 32) {m : Mem} {H : HashValue}
    (h : ∀ k (hk : k < 8), VG.Proof.Sha512.Arm.rd64 m st (8 * k) = H[k]) : stateAt m (State.addr st) = H := by
  ext k hk
  rw [VG.Proof.Sha512.Arm.stateAt_get hfit m hk, h k hk]

theorem cat44 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    ((b0 ++ b1 ++ b2 ++ b3 : BitVec 32) ++ (b4 ++ b5 ++ b6 ++ b7 : BitVec 32) : BitVec 64) =
      (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7 : BitVec 64) := by
  simp only [BitVec.append_assoc, BitVec.cast_eq]

theorem add_one' (p : Addr) (a : Nat) : p + BitVec.ofNat 64 a + 1 = p + BitVec.ofNat 64 (a + 1) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl

/-- `loadW` makes the block's words from its bytes. -/
theorem raw_block {bk : BitVec 32} (hfit : bk.toNat + 128 ≤ 2 ^ 32) (m : Mem) :
    VG.Proof.Sha512.Arm.Raw bk (blockAt m (State.addr bk)) m := by
  intro j hj
  rw [W_lt _ hj]
  simp only [blockAt, parseBlock, VG.Proof.Sha512.Arm.rd64, VG.Proof.Sha512.Arm.lo_append, VG.Proof.Sha512.Arm.hi_append]
  rw [VG.Proof.Sha512.Arm.A_eq (by omega), VG.Proof.Sha512.Arm.A_eq (by omega), rev_readW, rev_readW]
  simp only [VG.Proof.Sha512.Arm.add_one', Nat.add_assoc]
  exact VG.Proof.Sha512.Arm.cat44 _ _ _ _ _ _ _ _

/-! ## Loading the working variables -/

structure LdInv (st scr : BitVec 32) (s : State) (n : Nat) (s' : State) : Prop where
  gpr : ∀ r, r ∉ [X0, X1] → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  vars : ∀ k < n, VG.Proof.Sha512.Arm.rd64 s'.mem scr (8 * k) = VG.Proof.Sha512.Arm.rd64 s.mem st (8 * k)
  frame : Frame [VG.Proof.Sha512.Arm.workR scr] s.mem s'.mem

theorem Ctx.disjW {st scr : BitVec 32} {s : State} (c : VG.Proof.Sha512.Arm.Ctx st scr s) : (VG.Proof.Sha512.Arm.stR st).Disjoint (VG.Proof.Sha512.Arm.workR scr) :=
  c.disj.sub_right (Region.sub_prefix (by omega))

theorem load_ok {st scr : BitVec 32} {s : State} (c : VG.Proof.Sha512.Arm.Ctx st scr s) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap loadH)) s (VG.Proof.Sha512.Arm.LdInv st scr s n) := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ h => absurd h (by omega),
      Frame.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s₁ h₁ => ?_
    have c₁ := c.of_eq (h₁.gpr _ (by decide)) (h₁.gpr _ (by decide)) h₁.wr
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [loadH, ← List.append_nil (Impl.Sha512.Arm.st X0 X1 .r3 (8 * n))]
    refine VG.Proof.Sha512.Arm.wp_ld (by decide) (by decide) (by omega) c₁.r0 (c₁.wS _ (by omega)).1
      (c₁.wS _ (by omega)).2 fun s₂ o₂ p₂ => ?_
    refine VG.Proof.Sha512.Arm.wp_st (by omega) (by rw [o₂.gpr _ (by decide), c₁.r3]) p₂
      (by rw [o₂.wr]; exact (c₁.wV _ (by omega)).1) (by rw [o₂.wr]; exact (c₁.wV _ (by omega)).2)
      fun s₃ u₃ => WP.block_nil ⟨fun r hr => ?_, by rw [u₃.rd, o₂.rd, h₁.rd],
        by rw [u₃.wr, o₂.wr, h₁.wr], by rw [u₃.sp, o₂.sp, h₁.sp], fun k hk => ?_, ?_⟩
    · rw [u₃.gpr, o₂.gpr r hr, h₁.gpr r hr]
    · have fitV := c.fitV
      rw [u₃.mem]
      by_cases hkn : k = n
      · subst hkn
        rw [VG.Proof.Sha512.Arm.rd64_write64_self _ _ (by omega),
          VG.Proof.Sha512.Arm.rd64_frame h₁.frame (fun r hr => by simp at hr; subst hr; exact c.disjW) c.fitS (by omega)]
      · rw [VG.Proof.Sha512.Arm.rd64_write64_ne (b := scr) (o := 8 * n) (o' := 8 * k) _ _ (by omega) (by omega)
          (by omega), o₂.mem]
        exact h₁.vars k (by omega)
    · rw [u₃.mem, o₂.mem]
      exact VG.Proof.Sha512.Arm.frame_write64 (N := 192) (o := 8 * n) h₁.frame (by simp) (by have := c.fitV; omega) (by omega) _

/-! ## Adding them into the hash value -/

structure UInv (st scr : BitVec 32) (s : State) (n : Nat) (s' : State) : Prop where
  gpr : ∀ r, r ∉ [Z0, Z1, X0, X1] → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  done : ∀ k < n, VG.Proof.Sha512.Arm.rd64 s'.mem st (8 * k) = VG.Proof.Sha512.Arm.rd64 s.mem scr (8 * k) + VG.Proof.Sha512.Arm.rd64 s.mem st (8 * k)
  todo : ∀ k, n ≤ k → k < 8 → VG.Proof.Sha512.Arm.rd64 s'.mem st (8 * k) = VG.Proof.Sha512.Arm.rd64 s.mem st (8 * k)
  frame : Frame [VG.Proof.Sha512.Arm.stR st] s.mem s'.mem

theorem update_ok {st scr : BitVec 32} {s : State} (c : VG.Proof.Sha512.Arm.Ctx st scr s) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap addH)) s (VG.Proof.Sha512.Arm.UInv st scr s n) := by
  intro n hn
  have fitS := c.fitS
  induction n with
  | zero => exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ h => absurd h (by omega),
      fun _ _ _ => rfl, Frame.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s₁ h₁ => ?_
    have c₁ := c.of_eq (h₁.gpr _ (by decide)) (h₁.gpr _ (by decide)) h₁.wr
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [addH, List.append_assoc, List.append_assoc, ← List.append_nil (Impl.Sha512.Arm.st Z0 Z1 .r0 (8 * n))]
    refine VG.Proof.Sha512.Arm.wp_ld (by decide) (by decide) (by omega) c₁.r3 (c₁.wV _ (by omega)).1
      (c₁.wV _ (by omega)).2 fun s₂ o₂ p₂ => ?_
    refine VG.Proof.Sha512.Arm.wp_ld (by decide) (by decide) (by omega) (by rw [o₂.gpr _ (by decide), c₁.r0])
      (by rw [o₂.wr]; exact (c₁.wS _ (by omega)).1) (by rw [o₂.wr]; exact (c₁.wS _ (by omega)).2)
      fun s₃ o₃ p₃ => ?_
    refine VG.Proof.Sha512.Arm.wp_add64 (by decide) (by decide) (p₂.of_only o₃ (by decide) (by decide)) p₃
      fun s₄ o₄ p₄ => ?_
    have O := (o₂.trans o₃).trans o₄
    refine VG.Proof.Sha512.Arm.wp_st (by omega) (by rw [O.gpr _ (by decide), c₁.r0]) p₄
      (by rw [O.wr]; exact (c₁.wS _ (by omega)).1) (by rw [O.wr]; exact (c₁.wS _ (by omega)).2)
      fun s₅ u₅ => WP.block_nil ⟨fun r hr => ?_, by rw [u₅.rd, O.rd, h₁.rd],
        by rw [u₅.wr, O.wr, h₁.wr], by rw [u₅.sp, O.sp, h₁.sp], fun k hk => ?_, fun k hk hk' => ?_, ?_⟩
    · rw [u₅.gpr, (O.mono (by decide)).gpr r hr, h₁.gpr r hr]
    · rw [u₅.mem, O.mem, o₂.mem]
      by_cases hkn : k = n
      · subst hkn
        rw [VG.Proof.Sha512.Arm.rd64_write64_self _ _ (by omega), h₁.todo k (by omega) (by omega),
          VG.Proof.Sha512.Arm.rd64_frame h₁.frame (fun r hr => by simp at hr; subst hr; exact c.disj.symm) c.fitV
            (by omega)]
      · rw [VG.Proof.Sha512.Arm.rd64_write64_ne (b := st) (o := 8 * n) (o' := 8 * k) _ _ (by omega) (by omega)
          (by omega)]
        exact h₁.done k (by omega)
    · rw [u₅.mem, O.mem, VG.Proof.Sha512.Arm.rd64_write64_ne (b := st) (o := 8 * n) (o' := 8 * k) _ _ (by omega)
        (by omega) (by omega)]
      exact h₁.todo k (by omega) hk'
    · rw [u₅.mem, O.mem]
      exact VG.Proof.Sha512.Arm.frame_write64 (N := 64) (o := 8 * n) h₁.frame (by simp) c.fitS (by omega) _


namespace Compress

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev stp : BitVec 32 := s₀.gpr .r0
abbrev bp : BitVec 32 := s₀.gpr .r1
abbrev nb : Nat := (s₀.gpr .r2).toNat
abbrev scp : BitVec 32 := s₀.gpr .r3
abbrev blR : Region := ⟨State.addr (VG.Proof.Sha512.Arm.Compress.bp s₀), 128 * VG.Proof.Sha512.Arm.Compress.nb s₀⟩
abbrev H₀ : HashValue := stateAt s₀.mem (State.addr (VG.Proof.Sha512.Arm.Compress.stp s₀))

/-- Where block `i` starts. -/
abbrev blkAddr (i : Nat) : BitVec 32 := VG.Proof.Sha512.Arm.Compress.bp s₀ + BitVec.ofNat 32 (128 * i)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.Sha512.Arm.Compress.blR s₀]
  wr : s₀.wr = [VG.Proof.Sha512.Arm.stR (VG.Proof.Sha512.Arm.Compress.stp s₀), VG.Proof.Sha512.Arm.scrR (VG.Proof.Sha512.Arm.Compress.scp s₀)]
  st_scr : (VG.Proof.Sha512.Arm.stR (VG.Proof.Sha512.Arm.Compress.stp s₀)).Disjoint (VG.Proof.Sha512.Arm.scrR (VG.Proof.Sha512.Arm.Compress.scp s₀))
  blk_st : (VG.Proof.Sha512.Arm.Compress.blR s₀).Disjoint (VG.Proof.Sha512.Arm.stR (VG.Proof.Sha512.Arm.Compress.stp s₀))
  blk_scr : (VG.Proof.Sha512.Arm.Compress.blR s₀).Disjoint (VG.Proof.Sha512.Arm.scrR (VG.Proof.Sha512.Arm.Compress.scp s₀))
  st_fits : (VG.Proof.Sha512.Arm.Compress.stp s₀).toNat + 64 ≤ 2 ^ 32
  blk_fits : (VG.Proof.Sha512.Arm.Compress.bp s₀).toNat + 128 * VG.Proof.Sha512.Arm.Compress.nb s₀ ≤ 2 ^ 32
  scr_fits : (VG.Proof.Sha512.Arm.Compress.scp s₀).toNat + 224 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : Proof.Sha512.compressArm.pre s₀) : VG.Proof.Sha512.Arm.Compress.Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

namespace Pre
variable {s₀ : State} (h : VG.Proof.Sha512.Arm.Compress.Pre s₀)
include h

theorem ctx {s : State} (h0 : s.gpr .r0 = VG.Proof.Sha512.Arm.Compress.stp s₀) (h3 : s.gpr .r3 = VG.Proof.Sha512.Arm.Compress.scp s₀) (hw : s.wr = s₀.wr) :
    VG.Proof.Sha512.Arm.Ctx (VG.Proof.Sha512.Arm.Compress.stp s₀) (VG.Proof.Sha512.Arm.Compress.scp s₀) s :=
  ⟨h0, h3, h.st_fits, h.scr_fits, h.st_scr,
    Reg64.of_mem (by rw [hw, h.wr]; simp) h.st_fits, Reg64.of_mem (by rw [hw, h.wr]; simp) h.scr_fits⟩

theorem blk_toNat {i : Nat} (hi : i < VG.Proof.Sha512.Arm.Compress.nb s₀) : (VG.Proof.Sha512.Arm.Compress.blkAddr s₀ i).toNat = (VG.Proof.Sha512.Arm.Compress.bp s₀).toNat + 128 * i := by
  have := h.blk_fits
  simp only [VG.Proof.Sha512.Arm.Compress.blkAddr, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := 128 * i) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem blk_fit {i : Nat} (hi : i < VG.Proof.Sha512.Arm.Compress.nb s₀) : (VG.Proof.Sha512.Arm.Compress.blkAddr s₀ i).toNat + 128 ≤ 2 ^ 32 := by
  have := h.blk_fits; rw [h.blk_toNat hi]; omega

theorem blk_addr {i : Nat} (hi : i < VG.Proof.Sha512.Arm.Compress.nb s₀) :
    State.addr (VG.Proof.Sha512.Arm.Compress.blkAddr s₀ i) = State.addr (VG.Proof.Sha512.Arm.Compress.bp s₀) + BitVec.ofNat 64 (128 * i) :=
  addr_add (by have := h.blk_fits; omega)

theorem blk_sub {i : Nat} (hi : i < VG.Proof.Sha512.Arm.Compress.nb s₀) : Region.Sub ⟨State.addr (VG.Proof.Sha512.Arm.Compress.blkAddr s₀ i), 128⟩ (VG.Proof.Sha512.Arm.Compress.blR s₀) := by
  have := h.blk_fits
  rw [h.blk_addr hi]; exact sub_offset (by omega) (by omega)

theorem blk_rd {i : Nat} (hi : i < VG.Proof.Sha512.Arm.Compress.nb s₀) {o : Nat} (ho : o + 4 ≤ 128) :
    InRegions (s₀.rd ++ s₀.wr) (VG.Proof.Sha512.Arm.A (VG.Proof.Sha512.Arm.Compress.blkAddr s₀ i) o) 4 := by
  refine ⟨VG.Proof.Sha512.Arm.Compress.blR s₀, by simp [h.rd], ?_⟩
  have := h.blk_fit hi
  have := h.blk_fits
  have e : State.addr (VG.Proof.Sha512.Arm.Compress.bp s₀) + BitVec.ofNat 64 (128 * i) + BitVec.ofNat 64 o =
      State.addr (VG.Proof.Sha512.Arm.Compress.bp s₀) + BitVec.ofNat 64 (128 * i + o) := by
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  rw [VG.Proof.Sha512.Arm.A_eq (by omega), h.blk_addr hi, e]
  exact contains_offset (by omega) (by omega)

theorem blk_disj {i : Nat} (hi : i < VG.Proof.Sha512.Arm.Compress.nb s₀) :
    ∀ r ∈ [VG.Proof.Sha512.Arm.stR (VG.Proof.Sha512.Arm.Compress.stp s₀), VG.Proof.Sha512.Arm.scrR (VG.Proof.Sha512.Arm.Compress.scp s₀)], Region.Disjoint ⟨State.addr (VG.Proof.Sha512.Arm.Compress.blkAddr s₀ i), 128⟩ r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨h.blk_st.sub_left (h.blk_sub hi), h.blk_scr.sub_left (h.blk_sub hi)⟩

theorem in_save {d : Nat} (hd : d + 4 ≤ 224) :
    InRegions (s₀.rd ++ s₀.wr) (State.addr (VG.Proof.Sha512.Arm.Compress.scp s₀) + BitVec.ofNat 64 d) 4 :=
  ⟨VG.Proof.Sha512.Arm.scrR (VG.Proof.Sha512.Arm.Compress.scp s₀), by simp [h.wr], contains_offset hd (by omega)⟩

theorem out_save {d : Nat} (hd : d + 4 ≤ 224) : InRegions s₀.wr (State.addr (VG.Proof.Sha512.Arm.Compress.scp s₀) + BitVec.ofNat 64 d) 4 :=
  ⟨VG.Proof.Sha512.Arm.scrR (VG.Proof.Sha512.Arm.Compress.scp s₀), by simp [h.wr], contains_offset hd (by omega)⟩

end Pre

/-! ## The loop invariant -/

/-- The callee-saved registers are saved in the scratch buffer. -/
abbrev Saved (s₀ : State) (m : Mem) : Prop := Spill.Saved m (State.addr (VG.Proof.Sha512.Arm.Compress.scp s₀)) s₀.gpr saved

theorem saved_slots : Spill.Slots 192 224 saved := by decide

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = VG.Proof.Sha512.Arm.Compress.stp s₀
  r3 : s.gpr .r3 = VG.Proof.Sha512.Arm.Compress.scp s₀
  lr : s.gpr .lr = s₀.gpr .lr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [VG.Proof.Sha512.Arm.stR (VG.Proof.Sha512.Arm.Compress.stp s₀), VG.Proof.Sha512.Arm.scrR (VG.Proof.Sha512.Arm.Compress.scp s₀)] s₀.mem s.mem
  state : stateAt s.mem (State.addr (VG.Proof.Sha512.Arm.Compress.stp s₀)) =
    compressBlocks (VG.Proof.Sha512.Arm.Compress.H₀ s₀) s₀.mem (State.addr (VG.Proof.Sha512.Arm.Compress.bp s₀)) i
  saved : VG.Proof.Sha512.Arm.Compress.Saved s₀ s.mem

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends VG.Proof.Sha512.Arm.Compress.Common s₀ i s where
  r4 : s.gpr .r4 = VG.Proof.Sha512.Arm.Compress.blkAddr s₀ i
  r5 : s.gpr .r5 = BitVec.ofNat 32 (VG.Proof.Sha512.Arm.Compress.nb s₀ - i)

theorem saved_frame {s₀ : State} (hp : VG.Proof.Sha512.Arm.Compress.Pre s₀) {m m' : Mem} (h : VG.Proof.Sha512.Arm.Compress.Saved s₀ m)
    (hf : Frame [VG.Proof.Sha512.Arm.workR (VG.Proof.Sha512.Arm.Compress.scp s₀)] m m' ∨ Frame [VG.Proof.Sha512.Arm.stR (VG.Proof.Sha512.Arm.Compress.stp s₀)] m m') : VG.Proof.Sha512.Arm.Compress.Saved s₀ m' := by
  rcases hf with hf | hf <;> refine h.frame VG.Proof.Sha512.Arm.Compress.saved_slots hf fun r hr => ?_ <;> rw [List.mem_singleton.mp hr]
  · exact Offset.disjoint_base _ (by decide) (by decide)
  · exact Region.Disjoint.sub_left hp.st_scr.symm (Offset.sub_base _ (by decide))

/-! ## One block -/

theorem compressBlocks_succ (H : HashValue) (m : Mem) (p : Addr) (i : Nat) :
    compressBlocks H m p (i + 1) =
      compress (compressBlocks H m p i) (blockAt m (p + BitVec.ofNat 64 (128 * i))) := by
  simp [compressBlocks, List.range_succ, List.foldl_append]

theorem advance_ok {s : State} {Q : State → Prop}
    (k : ∀ s', s'.gpr .r4 = s.gpr .r4 + 128 → s'.gpr .r5 = s.gpr .r5 - 1 →
      s'.z = (s.gpr .r5 - 1 == 0) → (∀ r, r ≠ .r4 → r ≠ .r5 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → Q s') :
    WP isa (.block advance) s Q := by
  unfold advance
  refine wp_add (op2_imm (by decide)) fun s₁ u₁ =>
    wp_subs (op2_imm (by decide)) fun s₂ u₂ hz => WP.block_nil ?_
  refine k s₂ ?_ ?_ ?_ (fun r h4 h5 => ?_) ?_ ?_ ?_
  · rw [u₂.other _ (by decide), u₁.gpr]
  · rw [u₂.gpr, u₁.other _ (by decide)]
  · rw [hz, u₁.other _ (by decide)]
  · rw [u₂.other _ h5, u₁.other _ h4]
  · rw [u₂.mem, u₁.mem]
  · rw [u₂.rd, u₁.rd]
  · rw [u₂.wr, u₁.wr]

theorem body_ok {s₀ : State} (hp : VG.Proof.Sha512.Arm.Compress.Pre s₀) {i : Nat} (hi : i < VG.Proof.Sha512.Arm.Compress.nb s₀) {s : State}
    (hL : VG.Proof.Sha512.Arm.Compress.LInv s₀ i s) :
    WP isa body s fun s' =>
      (VG.Arm.eval .ne s' = some false ∧ VG.Proof.Sha512.Arm.Compress.Common s₀ (VG.Proof.Sha512.Arm.Compress.nb s₀) s') ∨
      (VG.Arm.eval .ne s' = some true ∧ i + 1 < VG.Proof.Sha512.Arm.Compress.nb s₀ ∧ VG.Proof.Sha512.Arm.Compress.LInv s₀ (i + 1) s') := by
  have c := hp.ctx hL.r0 hL.r3 hL.wr
  have fitS := hp.st_fits
  have fitV := hp.scr_fits
  have fitB := hp.blk_fit hi
  set H := stateAt s.mem (State.addr (VG.Proof.Sha512.Arm.Compress.stp s₀)) with hH
  set M := blockAt s₀.mem (State.addr (VG.Proof.Sha512.Arm.Compress.blkAddr s₀ i)) with hMdef
  refine WP.seq (WP.mono (VG.Proof.Sha512.Arm.load_ok c 8 (Nat.le_refl _)) fun s₁ h₁ => ?_)
  have c₁ := c.of_eq (h₁.gpr _ (by decide)) (h₁.gpr _ (by decide)) h₁.wr
  have hB : VG.Proof.Sha512.Arm.BlkCtx (VG.Proof.Sha512.Arm.Compress.scp s₀) (VG.Proof.Sha512.Arm.Compress.blkAddr s₀ i) s₁ :=
    ⟨by rw [h₁.gpr _ (by decide), hL.r4], fitB,
      (hp.blk_scr.sub_left (hp.blk_sub hi)).sub_right (Region.sub_prefix (by omega)),
      fun o ho => by rw [h₁.rd, h₁.wr, hL.rd, hL.wr]; exact hp.blk_rd hi ho⟩
  have hM : VG.Proof.Sha512.Arm.Raw (VG.Proof.Sha512.Arm.Compress.blkAddr s₀ i) M s₁.mem := fun j hj => by
    rw [VG.Proof.Sha512.Arm.rd64_frame h₁.frame (fun r hr => by simp at hr; subst hr; exact hB.disj) fitB (by omega),
      VG.Proof.Sha512.Arm.rd64_frame hL.frame (hp.blk_disj hi) fitB (by omega)]
    exact VG.Proof.Sha512.Arm.raw_block fitB s₀.mem j hj
  have h0 : ∀ k (hk : k < 8), VG.Proof.Sha512.Arm.rd64 s₁.mem (VG.Proof.Sha512.Arm.Compress.scp s₀) (8 * k) = H[k] := fun k hk => by
    rw [h₁.vars k hk, VG.Proof.Sha512.Arm.stateAt_get fitS _ hk]
  refine WP.seq (WP.mono (VG.Proof.Sha512.Arm.rounds_ok c₁ hB hM h0 80 (Nat.le_refl _)) fun s₂ h₂ => ?_)
  have c₂ := c₁.of_rinv h₂
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Sha512.Arm.update_ok c₂ 8 (Nat.le_refl _)) fun s₃ h₃ => VG.Proof.Sha512.Arm.Compress.advance_ok fun s₄ r4₄ r5₄ z₄ g₄ m₄ rd₄ wr₄ => ?_
  -- Registers
  have g₃ : ∀ r, r ∉ VG.Proof.Sha512.Arm.temps → r ≠ .r4 → r ≠ .r5 → s₄.gpr r = s.gpr r := fun r hr h4 h5 => by
    have e₃ : ∀ r ∈ [Z0, Z1, X0, X1], r ∈ VG.Proof.Sha512.Arm.temps := by decide
    have e₁ : ∀ r ∈ [X0, X1], r ∈ VG.Proof.Sha512.Arm.temps := by decide
    rw [g₄ r h4 h5, h₃.gpr r fun h => hr (e₃ r h), h₂.gpr r hr, h₁.gpr r fun h => hr (e₁ r h)]
  have gT : ∀ r, r ∉ VG.Proof.Sha512.Arm.temps → s₃.gpr r = s.gpr r := fun r hr => by
    have e₃ : ∀ r ∈ [Z0, Z1, X0, X1], r ∈ VG.Proof.Sha512.Arm.temps := by decide
    have e₁ : ∀ r ∈ [X0, X1], r ∈ VG.Proof.Sha512.Arm.temps := by decide
    rw [h₃.gpr r fun h => hr (e₃ r h), h₂.gpr r hr, h₁.gpr r fun h => hr (e₁ r h)]
  have hrd : s₄.rd = s₀.rd := by rw [rd₄, h₃.rd, h₂.rd, h₁.rd, hL.rd]
  have hwr : s₄.wr = s₀.wr := by rw [wr₄, h₃.wr, h₂.wr, h₁.wr, hL.wr]
  -- Memory
  have hframe : Frame [VG.Proof.Sha512.Arm.stR (VG.Proof.Sha512.Arm.Compress.stp s₀), VG.Proof.Sha512.Arm.scrR (VG.Proof.Sha512.Arm.Compress.scp s₀)] s₀.mem s₄.mem := by
    have sw : ∀ r ∈ [VG.Proof.Sha512.Arm.workR (VG.Proof.Sha512.Arm.Compress.scp s₀)], ∃ r' ∈ [VG.Proof.Sha512.Arm.stR (VG.Proof.Sha512.Arm.Compress.stp s₀), VG.Proof.Sha512.Arm.scrR (VG.Proof.Sha512.Arm.Compress.scp s₀)], Region.Sub r r' :=
      fun r hr => ⟨VG.Proof.Sha512.Arm.scrR (VG.Proof.Sha512.Arm.Compress.scp s₀), by simp, by simp at hr; subst hr; exact Region.sub_prefix (by omega)⟩
    rw [m₄]
    exact ((hL.frame.trans (h₁.frame.sub sw)).trans (h₂.frame.sub sw)).trans (h₃.frame.mono (by simp))
  have hstate : stateAt s₄.mem (State.addr (VG.Proof.Sha512.Arm.Compress.stp s₀)) = compress H M := by
    rw [m₄]
    refine VG.Proof.Sha512.Arm.stateAt_ext fitS fun k hk => ?_
    have hd₁ : ∀ r ∈ [VG.Proof.Sha512.Arm.workR (VG.Proof.Sha512.Arm.Compress.scp s₀)], Region.Disjoint (VG.Proof.Sha512.Arm.stR (VG.Proof.Sha512.Arm.Compress.stp s₀)) r := fun r hr => by
      simp at hr; subst hr; exact c.disjW
    rw [h₃.done k hk, show 8 * k = vOff 80 k by simp only [vOff]; omega, h₂.vars k hk,
      show vOff 80 k = 8 * k by simp only [vOff]; omega, h₂.hash k hk,
      VG.Proof.Sha512.Arm.rd64_frame h₁.frame hd₁ fitS (by omega), ← VG.Proof.Sha512.Arm.stateAt_get fitS _ hk]
    simp only [Spec.Sha512.compress, Vector.getElem_zipWith]
    rfl
  have hsaved : VG.Proof.Sha512.Arm.Compress.Saved s₀ s₄.mem := by
    rw [m₄]
    refine VG.Proof.Sha512.Arm.Compress.saved_frame hp ?_ (.inr h₃.frame)
    refine VG.Proof.Sha512.Arm.Compress.saved_frame hp ?_ (.inl h₂.frame)
    exact VG.Proof.Sha512.Arm.Compress.saved_frame hp hL.saved (.inl h₁.frame)
  have hnb : VG.Proof.Sha512.Arm.Compress.nb s₀ < 2 ^ 32 := (s₀.gpr .r2).isLt
  have hr5 : s₃.gpr .r5 - 1 = BitVec.ofNat 32 (VG.Proof.Sha512.Arm.Compress.nb s₀ - (i + 1)) := by
    rw [gT .r5 (by decide), hL.r5, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have hcommon : VG.Proof.Sha512.Arm.Compress.Common s₀ (i + 1) s₄ := by
    refine ⟨by rw [g₃ _ (by decide) (by decide) (by decide), hL.r0],
      by rw [g₃ _ (by decide) (by decide) (by decide), hL.r3],
      by rw [g₃ _ (by decide) (by decide) (by decide), hL.lr], hrd, hwr, hframe, ?_, hsaved⟩
    rw [hstate, VG.Proof.Sha512.Arm.Compress.compressBlocks_succ, ← hL.state, hMdef, hp.blk_addr hi]
  have hev : VG.Arm.eval .ne s₄ = some (!(BitVec.ofNat 32 (VG.Proof.Sha512.Arm.Compress.nb s₀ - (i + 1)) == 0)) := by
    rw [eval_ne, z₄, hr5]
  by_cases hlast : i + 1 = VG.Proof.Sha512.Arm.Compress.nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon⟩
  · right
    have hne : VG.Proof.Sha512.Arm.Compress.nb s₀ - (i + 1) ≠ 0 := by omega
    have h0 : BitVec.ofNat 32 (VG.Proof.Sha512.Arm.Compress.nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
      exact hne h'
    refine ⟨by rw [hev]; simpa using h0, by omega, { hcommon with r4 := ?_, r5 := ?_ }⟩
    · rw [r4₄, gT .r4 (by decide), hL.r4]
      simp only [VG.Proof.Sha512.Arm.Compress.blkAddr]
      rw [BitVec.add_assoc, show (128 : BitVec _) = BitVec.ofNat _ 128 from rfl, BitVec.ofNat_add_ofNat]
      rfl
    · rw [r5₄, hr5]

/-! ## Prologue and epilogue -/

/-- The memory after the prologue. -/
def saveMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (State.addr (VG.Proof.Sha512.Arm.Compress.scp s₀)) s₀.gpr saved

theorem save_ok {s₀ : State} (hp : VG.Proof.Sha512.Arm.Compress.Pre s₀) :
    WP isa (.block save) s₀ fun s₁ =>
      s₁.gpr = s₀.gpr ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.mem = VG.Proof.Sha512.Arm.Compress.saveMem s₀ := by
  rw [save, ← List.append_nil (saved.map _)]
  exact Spill.save_slots_ok VG.Proof.Sha512.Arm.Compress.saved_slots hp.scr_fits (fun _ _ hd => hp.out_save hd)
    (WP.block_nil ⟨rfl, rfl, rfl, rfl⟩)

theorem saveMem_saved (s₀ : State) : VG.Proof.Sha512.Arm.Compress.Saved s₀ (VG.Proof.Sha512.Arm.Compress.saveMem s₀) := Spill.saveMem_saved _ _ _ _ VG.Proof.Sha512.Arm.Compress.saved_slots

theorem saveMem_frame (s₀ : State) : Frame [VG.Proof.Sha512.Arm.scrR (VG.Proof.Sha512.Arm.Compress.scp s₀)] s₀.mem (VG.Proof.Sha512.Arm.Compress.saveMem s₀) :=
  Spill.saveMem_frame _ _ _ (by decide) saved (by decide)

theorem common_zero {s₀ : State} (hp : VG.Proof.Sha512.Arm.Compress.Pre s₀) {s₁ : State} (h0 : s₁.gpr .r0 = s₀.gpr .r0)
    (h3 : s₁.gpr .r3 = s₀.gpr .r3) (hlr : s₁.gpr .lr = s₀.gpr .lr)
    (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (hm : s₁.mem = VG.Proof.Sha512.Arm.Compress.saveMem s₀) : VG.Proof.Sha512.Arm.Compress.Common s₀ 0 s₁ := by
  refine ⟨h0, h3, hlr, hrd, hwr, ?_, ?_, by rw [hm]; exact VG.Proof.Sha512.Arm.Compress.saveMem_saved s₀⟩
  · rw [hm]; exact (VG.Proof.Sha512.Arm.Compress.saveMem_frame s₀).mono (by simp)
  · rw [hm]
    have hd : ∀ r ∈ [VG.Proof.Sha512.Arm.scrR (VG.Proof.Sha512.Arm.Compress.scp s₀)], Region.Disjoint (VG.Proof.Sha512.Arm.stR (VG.Proof.Sha512.Arm.Compress.stp s₀)) r := fun r hr => by
      simp at hr; subst hr; exact hp.st_scr
    refine VG.Proof.Sha512.Arm.stateAt_ext hp.st_fits fun k hk => ?_
    rw [VG.Proof.Sha512.Arm.rd64_frame (VG.Proof.Sha512.Arm.Compress.saveMem_frame s₀) hd hp.st_fits (by omega), ← VG.Proof.Sha512.Arm.stateAt_get hp.st_fits _ hk]
    simp [compressBlocks]

theorem restore_ok {s₀ : State} (hp : VG.Proof.Sha512.Arm.Compress.Pre s₀) {s : State} (hc : VG.Proof.Sha512.Arm.Compress.Common s₀ (VG.Proof.Sha512.Arm.Compress.nb s₀) s) :
    WP isa (.block restore) s fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha512.compressArm.post s₀ s' := by
  rw [restore, ← List.append_nil (saved.map _)]
  refine Spill.restore_slots_ok VG.Proof.Sha512.Arm.Compress.saved_slots (by decide) (g := s₀.gpr) (by rw [hc.r3]; exact hp.scr_fits)
    (fun _ _ hd => by rw [hc.rd, hc.wr, hc.r3]; exact hp.in_save hd) (by rw [hc.r3]; exact hc.saved)
    fun s' hs ho hm _ _ _ => WP.block_nil ⟨fun r hr => ?_, (congrArg (stateAt · _) hm).trans hc.state⟩
  by_cases h : r = .lr
  · subst h; rw [ho _ (by decide), hc.lr]
  · have hk : ∀ r ∈ preserved, r ≠ .lr → r ∈ saved.map Prod.fst := by decide
    exact Spill.restored_reg hs (hk r hr h)

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : VG.Proof.Sha512.Arm.Compress.Pre s₀) :
    WP isa Impl.Sha512.Arm.compress s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha512.compressArm.post s₀ s' := by
  unfold Impl.Sha512.Arm.compress
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Sha512.Arm.Compress.save_ok hp) fun s₁ ⟨hg, hrd, hwr, hm⟩ => ?_
  refine wp_mov (op2_reg _ _) fun s₂ u₂ => wp_mov (op2_reg _ _) fun s₃ u₃ =>
    wp_cmp (op2_imm (by decide)) fun s₄ u₄ hz => WP.block_nil ?_
  have g : ∀ r, r ≠ .r4 → r ≠ .r5 → s₄.gpr r = s₀.gpr r := fun r h4 h5 => by
    rw [u₄.gpr, u₃.other _ h5, u₂.other _ h4, hg]
  refine WP.seq (WP.mono (Q := VG.Proof.Sha512.Arm.Compress.Common s₀ (VG.Proof.Sha512.Arm.Compress.nb s₀)) ?_ fun s₅ hc => VG.Proof.Sha512.Arm.Compress.restore_ok hp hc)
  have hc₀ := VG.Proof.Sha512.Arm.Compress.common_zero hp (g _ (by decide) (by decide)) (g _ (by decide) (by decide))
    (g _ (by decide) (by decide)) (by rw [u₄.rd, u₃.rd, u₂.rd, hrd]) (by rw [u₄.wr, u₃.wr, u₂.wr, hwr])
    (by rw [u₄.mem, u₃.mem, u₂.mem, hm])
  have hr2 : s₃.gpr .r2 = s₀.gpr .r2 := by rw [u₃.other _ (by decide), u₂.other _ (by decide), hg]
  rw [hr2] at hz
  refine WP.ite (s₀.gpr .r2 - 0 == 0) (by simp [VG.Arm.eval, hz]) (fun h => ?_) (fun h => ?_)
  · have h0 : VG.Proof.Sha512.Arm.Compress.nb s₀ = 0 := by simp at h; simp [VG.Proof.Sha512.Arm.Compress.nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < VG.Proof.Sha512.Arm.Compress.nb s₀ := by
      simp only [beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = VG.Proof.Sha512.Arm.Compress.nb s₀ - i ∧ i < VG.Proof.Sha512.Arm.Compress.nb s₀ ∧ VG.Proof.Sha512.Arm.Compress.LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (VG.Arm.eval .ne s' = some false ∧ VG.Proof.Sha512.Arm.Compress.Common s₀ (VG.Proof.Sha512.Arm.Compress.nb s₀) s') ∨
        (VG.Arm.eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (VG.Proof.Sha512.Arm.Compress.body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, VG.Proof.Sha512.Arm.Compress.nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
    have hL₀ : VG.Proof.Sha512.Arm.Compress.LInv s₀ 0 s₄ :=
      { hc₀ with
        r4 := by rw [u₄.gpr, u₃.other _ (by decide), u₂.gpr, hg]; simp [VG.Proof.Sha512.Arm.Compress.blkAddr]
        r5 := by rw [u₄.gpr, u₃.gpr, u₂.other _ (by decide), hg]; simp [VG.Proof.Sha512.Arm.Compress.nb] }
    exact WP.loop (M := isa) Inv hstep (VG.Proof.Sha512.Arm.Compress.nb s₀) s₄ ⟨0, rfl, hpos, hL₀⟩

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x3000, 224⟩]

theorem compress_verified :
    Verified Arm.target Impl.Sha512.Arm.compress Proof.Sha512.compressArm := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, h₂⟩ := VG.Proof.Sha512.Arm.Compress.correct (VG.Proof.Sha512.Arm.Compress.pre_of s hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he⟩, h₂⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3]) ?_
      (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · refine ⟨VG.Proof.Sha512.Arm.Compress.satState, rfl, rfl, ?_, ?_, ?_, by decide, by decide, by decide⟩ <;>
    exact Region.disjoint_of_sep (by decide)

end Compress

end VG.Proof.Sha512.Arm

end

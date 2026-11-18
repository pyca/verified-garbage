module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.AffineSpec
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.SelectBase
public import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Call
public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Recode
public import VerifiedGarbage.Proof.X448.AArch64.Base.AddDefs
import VerifiedGarbage.Proof.X448.AArch64.Iter
import VerifiedGarbage.Proof.Ed448.AArch64.Window.Select
import VerifiedGarbage.Proof.X448.AArch64.BitWrite
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.X448.AArch64.Fast
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.AArch64.Mem
public import VerifiedGarbage.Spec.Ed448
public import VerifiedGarbage.Proof.Ed448.AArch64.Window.TableInit
import VerifiedGarbage.Proof.X448.AArch64.Weak.Counters
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Const
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Impl.Ed448.AArch64.VerifyWindow
import VerifiedGarbage.Proof.X448.AArch64.Fast.Weave
import VerifiedGarbage.Proof.Ed448.AArch64.Point56.AsFn
public import VerifiedGarbage.Proof.Ed448.AArch64.Window.Table
import VerifiedGarbage.TCB.AArch64.Isa
public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Table
public import VerifiedGarbage.Proof.Ed448.WnafWide.Group
import VerifiedGarbage.Proof.X448.BaseAdd
import VerifiedGarbage.Proof.X448.AArch64.Base.AddGen
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! ### `Ed448.AArch64.Sparse.Table`, which this module and modules that import it used -/

section

/-! ### `Ed448.AArch64.Sparse.OddLoop`, which only this module used -/

section

/-! Generate eight odd multiples using one doubling and seven projective additions. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64 (TAB)
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.X448.AArch64 (slot ACC)
open VG.Proof.X448.AArch64 (Scr Keeps Outside Outside2 limbs word ofs)
open VG.Proof.X448.AArch64.Weak (Index)
open VG.Proof.X448.AArch64.Fast (BEnv Same)
open VG.Proof.Curve448.AArch64.Fast (Ib Mb)
open VG.Proof.X448.AArch64.Base (pt zero_env next_ok)
open VG.Proof.Ed448.AArch64.Window (TPt TBnd tw tabStore_ok tabStore_pt tabStore_bnd
  TPt_outside TPt_of_tw tw_outside)
open VG.Proof.Ed448.WnafWide (oddPoint)
open VG.Spec.Ed448 (Point)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

def OddTabOk (m:Mem) (base:Addr) (P:Point) (k:Nat) : Prop :=
  ∀ e<k,TPt m base e=oddPoint P e ∧ TBnd m base e

def OddFrame (base:Addr) (m m':Mem) : Prop :=
  ∀ x,(ofs base x<64 ∨ 2880≤ofs base x) →
    (ofs base x<ACC ∨ ACC+1152≤ofs base x) →
    (ofs base x<TAB ∨ TAB+1536≤ofs base x) → m' x=m x

theorem OddFrame.trans {base:Addr} {m n p:Mem} (h:OddFrame base m n) (g:OddFrame base n p) :
    OddFrame base m p:=fun x a b c => (g x a b c).trans (h x a b c)

theorem OddFrame.of_outside2 {base:Addr} {m m':Mem} (h:Outside2 base 64 2816 ACC 1152 m m') :
    OddFrame base m m':=fun x a b _ => h x a b

theorem OddFrame.of_entry {base:Addr} {m m':Mem} {e:Nat} (he:e<8)
    (h:Outside base (TAB+192*e) 192 m m') : OddFrame base m m':=fun x _ _ c =>
  h x (by simp only [TAB] at c ⊢;omega_using [he, c])

structure OddInv (s₀:State) (base:Addr) (P:Point) (k:Nat) (s:State) : Prop where
  bound : 1≤k ∧ k≤8
  scr : Scr s base
  env : BEnv s.mem base
  zero : ∀ w<8,limbs s.mem base (slot (19:Index).val) w=0
  counter : s.gpr .x19=BitVec.ofNat 64 k
  acc : pt (EV s.mem base) 3 4 5=oddPoint P (k-1)
  pnt : pt (EV s.mem base) 6 7 8=VG.Proof.Ed448.double P
  one : EV s.mem base 20=EV s₀.mem base 20
  tab : OddTabOk s.mem base P k
  xbound : ∀ e<k,∀ w<8,(tw s.mem base e w).toNat<Mb
  chk : s.gpr .x20=s₀.gpr .x20
  rd : s.rd=s₀.rd
  wr : s.wr=s₀.wr
  mem : OddFrame base s₀.mem s.mem

theorem oddBody_ok {s₀ s : State} {base : Addr} {P : Point} {k : Nat} (h : OddInv s₀ base P k s) (hk : k < 8) :
    WP isa tableBody s fun t => (t.gpr .x9 != 0) = decide (k + 1 ≠ 8) ∧ OddInv s₀ base P (k + 1) t := by
  obtain ⟨hb2, hs, hb, hz, hc, hacc, hpnt, hone, htab, hxb, hchk, hrd, hwr, hmem⟩ := h
  rw [tableBody, WP.seq_iff]
  refine WP.mono (Point56.addCall_ok hs hb (zero_env hz).2) fun t1 ⟨k1, b1, s1, mx1, _, _, e1, _⟩ => ?_
  have hs1 := k1.scr hs
  have hc1 : t1.gpr .x19 = BitVec.ofNat 64 k := by rw [k1.regs.1 _ (by decide)]; exact hc
  rw [WP.block_append_iff]
  refine WP.mono (tabStore_ok hs1 (by omega_using [hk]) hc1) fun t2 ⟨w2, o2, k2⟩ => ?_
  have hs2 : Scr t2 base := hs1.of_keeps k2 (by decide)
  have hc2 : t2.gpr .x19 = BitVec.ofNat 64 k := by rw [k2.1 _ (by decide)]; exact hc1
  refine WP.mono (next_ok t2 (n := 8) (by decide) hk hc2) fun t3 ⟨c3, n3, k3, m3⟩ => ⟨n3, ?_⟩
  -- The slots after the addition, and the entries after the store.
  have z1 : ∀ w < 8, limbs t1.mem base (slot (19 : Index).val) w = 0 := fun w hw => by
    rw [s1 19 (by decide) w hw]; exact hz w hw
  have e3 : ∀ i : Index, EV t3.mem base i = EV t1.mem base i := fun i => by
    have := i.isLt
    simp only [VG.Proof.X448.AArch64.Weak.E, VG.Proof.X448.AArch64.Weak.F]
    refine congrArg _ (VG.Proof.X448.Wide.valN_congr fun w hw => ?_)
    rw [m3, o2.limbs (Or.inl (by simp only [slot, TAB]; omega_using [])) (by simp only [slot]; omega_using []) (by omega_using [hw])]
  have hacc1 : pt (EV t1.mem base) 3 4 5 = oddPoint P k := by
    rw [e1, Point56.genEnv_pt, (zero_env hz).1, VG.Proof.X448.AArch64.Base.genPt_eq, hacc, hpnt]
    conv_rhs => rw [show k=k-1+1 by omega_using [hb2], oddPoint]
  have hpnt1 : pt (EV t1.mem base) 6 7 8 = VG.Proof.Ed448.double P := by
    rw [← hpnt]; simp only [pt]
    rw [Same.env s1 (i := 6) (by decide), Same.env s1 (i := 7) (by decide), Same.env s1 (i := 8) (by decide)]
  refine ⟨⟨by omega_using [], by omega_using [hk]⟩, hs2.of_keeps k3 (by decide), ?_, fun w hw => ?_, c3, ?_, ?_, ?_, fun e he => ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro i w hw
    have := i.isLt
    show limbs t3.mem base (slot i.val) w < Ib
    rw [m3, o2.limbs (Or.inl (by simp only [slot, TAB]; omega_using [])) (by simp only [slot]; omega_using []) (by omega_using [hw])]
    exact b1 i w hw
  · rw [m3, o2.limbs (Or.inl (by simp only [slot, TAB]; omega_using [])) (by simp only [slot]; omega_using []) (by omega_using [hw])]
    exact z1 w hw
  · simp only [pt]; rw [e3 3, e3 4, e3 5, Nat.add_sub_cancel]; exact hacc1
  · simp only [pt]; rw [e3 6, e3 7, e3 8]; exact hpnt1
  · rw [e3 20, ← hone]; exact Same.env s1 (i := 20) (by decide)
  · rw [m3]
    by_cases hek : e = k
    · subst hek
      exact ⟨by rw [tabStore_pt w2, hacc1], tabStore_bnd b1 w2⟩
    · have ⟨te, tb⟩ := htab e (by omega_using [he, hek])
      have hmem1 : ∀ w < 24, tw t1.mem base e w = tw s.mem base e w := fun w hw => by
        unfold tw
        exact k1.mem.word (Or.inr (by simp only [TAB]; omega_using [])) (Or.inr (by simp only [ACC, TAB]; omega_using []))
          (by simp only [TAB]; omega_using [hk, he, hw])
      refine ⟨?_, fun w hw => ?_⟩
      · rw [TPt_outside o2 hek (by omega_using [hk, he]), TPt_of_tw hmem1, te]
      · rw [tw_outside o2 hek (by omega_using [hk, he]) hw, hmem1 w hw]; exact tb w hw
  · intro e he w hw
    rw [m3]
    by_cases hek:e=k
    · subst e
      rw [tw,w2 w (by omega_using [hw])]
      have heq:Window.src w=slot 3+8*w:=by
        simp only [Window.src,slot]
        omega_using [hw]
      rw [heq]
      exact mx1 w hw
    · rw [tw_outside o2 hek (by omega_using [hk, he]) (by omega_using [hw])]
      have hm:tw t1.mem base e w=tw s.mem base e w:=
        k1.mem.word (Or.inr (by simp only [TAB];omega_using [])) (Or.inr (by simp only [ACC,TAB];omega_using []))
          (by simp only [TAB];omega_using [hk, he, hw])
      rw [hm]
      exact hxb e (by omega_using [he, hek]) w hw
  · rw [k3.1 _ (by decide), k2.1 _ (by decide), k1.regs.1 _ (by decide)]; exact hchk
  · rw [k3.2.1, k2.2.1, k1.regs.2.1]; exact hrd
  · rw [k3.2.2, k2.2.2, k1.regs.2.2]; exact hwr
  · rw [m3]
    exact hmem.trans ((OddFrame.of_outside2 k1.mem).trans (OddFrame.of_entry hk o2))

theorem oddLoop_ok {s₀ : State} {base : Addr} {P : Point} :
    ∀ m, ∀ s, 1 ≤ m → m ≤ 7 → OddInv s₀ base P (8 - m) s →
      WP isa (.loop tableBody (.nonzero .x .x9)) s fun t => OddInv s₀ base P 8 t := by
  intro m s h1 h2 hi
  refine WP.loop (M := isa) (body := tableBody) (c := .nonzero .x .x9)
    (Q := fun t => OddInv s₀ base P 8 t)
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 7 ∧ OddInv s₀ base P (8 - m) s) ?_ m s ⟨h1, h2, hi⟩
  intro m s ⟨h1, h2, hi⟩
  refine WP.mono (oddBody_ok hi (by omega_using [h1])) fun t ⟨hz, ht⟩ => ?_
  simp only [eval, State.read, BitVec.setWidth_eq, hz]
  by_cases hm : m = 1
  · subst hm
    exact .inl ⟨by decide, ht⟩
  · refine .inr ⟨congrArg some (decide_eq_true (by omega_using [hm])), m - 1, by omega_using [h1], by omega_using [h1, hm], by omega_using [h2], ?_⟩
    rw [show 8 - (m - 1) = 8 - m + 1 by omega_using [h1, h2]]
    exact ht


end VG.Proof.Ed448.AArch64.Sparse

end

end

/-! ### `Ed448.AArch64.Window.Cross`, which this module and modules that import it used -/

section

/-!
# Ed448 verification on AArch64: the points compared

Untrusted: everything here is checked by Lean. What the comparison of `Q` and
`R` leaves, both doubled twice (`dbl2`): the products `X_Q Z_R`, `X_R Z_Q`,
`Y_Q Z_R`, `Y_R Z_Q` in slots 12–15 (`Cross`), the registers it may write
(`crossClob`), and copies of slots (`copy3_ok`, `pt_of_limbs`, `bnd_copy`).
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Window

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (ld st slot ACC)
open VG.Impl.X448.AArch64.Base (constSlot limb)
open VG.Impl.X448.AArch64.Fast (ops codeOf)
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 ofs)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd FKeep Same block_codeOf ops_append mulOp)
open VG.Proof.Ed448.AArch64.Point56 (mulOpK)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448.AArch64.Base (pt genEnv genPt temps addOps_ok zero_env constSlot_ok bnd_of_words F_of_words)
open VG.Spec.Ed448 (Point)
open VG.Proof.X448 (addPt)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- Two doublings. -/
def dbl2 (p : Point) : Point := VG.Proof.Ed448.double (VG.Proof.Ed448.double p)

/-- What the comparison leaves in slots 12–15, for `Q` and `R`. -/
structure Cross (Q R : Point) (e : Env) : Prop where
  c12 : e 12 = (dbl2 Q).X * (dbl2 R).Z
  c13 : e 13 = (dbl2 R).X * (dbl2 Q).Z
  c14 : e 14 = (dbl2 Q).Y * (dbl2 R).Z
  c15 : e 15 = (dbl2 R).Y * (dbl2 Q).Z

/-- Three slots copied from three others, among bounded ones: the copies' limbs, and every
other slot's kept. -/
theorem copy3_ok {s : State} {base : Addr} (hs : Scr s base) (o a : Nat) (ho : o + 3 ≤ 22) (ha : a + 3 ≤ 22)
    (hsep : o + 3 ≤ a ∨ a + 3 ≤ o) :
    WP isa (.block (Impl.Curve448.AArch64.copy (slot o) (slot a) ++ Impl.Curve448.AArch64.copy (slot (o + 1))
        (slot (a + 1)) ++ Impl.Curve448.AArch64.copy (slot (o + 2)) (slot (a + 2)))) s fun t =>
      (∀ c < 3, ∀ j < 8, limbs t.mem base (slot (o + c)) j = limbs s.mem base (slot (a + c)) j) ∧
      (∀ i : Index, (i.val < o ∨ o + 3 ≤ i.val) → ∀ j < 8, limbs t.mem base (slot i.val) j =
        limbs s.mem base (slot i.val) j) ∧
      Outside base (slot o) 384 s.mem t.mem ∧ Keeps VG.Proof.X448.AArch64.clob s t := by
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copyS_ok hs (o := slot o) (a := slot a) (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith)
    (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith)) fun t1 ⟨v1, o1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  refine WP.mono (copyS_ok hs1 (o := slot (o + 1)) (a := slot (a + 1)) (by simp only [slot]; omega_arith)
    (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith)
    (by simp only [slot]; omega_arith)) fun t2 ⟨v2, o2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  refine WP.mono (copyS_ok hs2 (o := slot (o + 2)) (a := slot (a + 2)) (by simp only [slot]; omega_arith)
    (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith)
    (by simp only [slot]; omega_arith)) fun t ⟨v3, o3, k3⟩ => ⟨fun c hc j hj => ?_, fun i hi j hj => ?_, ?_,
      (k1.trans k2).trans k3⟩
  · rcases (show c = 0 ∨ c = 1 ∨ c = 2 by omega_arith) with rfl | rfl | rfl
    · rw [o3.limbs (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) (by omega_arith),
        o2.limbs (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) (by omega_arith), Nat.add_zero, v1 j hj,
        Nat.add_zero]
    · rw [o3.limbs (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) (by omega_arith), v2 j hj,
        o1.limbs (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) (by omega_arith)]
    · rw [v3 j hj, o2.limbs (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) (by omega_arith),
        o1.limbs (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) (by omega_arith)]
  · have := i.isLt
    rw [o3.limbs (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) (by omega_arith),
      o2.limbs (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) (by omega_arith),
      o1.limbs (by simp only [slot]; omega_arith) (by simp only [slot]; omega_arith) (by omega_arith)]
  · intro x hx
    rw [o3 x (by simp only [slot] at hx ⊢; omega_arith), o2 x (by simp only [slot] at hx ⊢; omega_arith),
      o1 x (by simp only [slot] at hx ⊢; omega_arith)]

theorem pt_of_limbs {m m' : Mem} {base : Addr} {o a : Nat}
    (h : ∀ c < 3, ∀ j < 8, limbs m' base (slot (o + c)) j = limbs m base (slot (a + c)) j)
    {x y z x' y' z' : Index} (hx : x.val = o) (hy : y.val = o + 1) (hz : z.val = o + 2) (hx' : x'.val = a)
    (hy' : y'.val = a + 1) (hz' : z'.val = a + 2) : pt (EV m' base) x y z = pt (EV m base) x' y' z' := by
  simp only [pt, VG.Proof.X448.AArch64.Weak.E]
  rw [hx, hy, hz, hx', hy', hz']
  rw [FV_of_limbs (o := slot a) (o' := slot o) (fun j hj => by simpa using h 0 (by decide) j hj),
    FV_of_limbs (h 1 (by decide)), FV_of_limbs (h 2 (by decide))]

/-- The registers the comparison may write. -/
def crossClob : List Reg := .x30 :: .x4 :: VG.Proof.Curve448.AArch64.Fast.clob ++ VG.Proof.X448.AArch64.clob

theorem crossClob_ckeep {s t : State} {base : Addr} (h : Point56.CKeep base s t) : Keeps crossClob s t :=
  h.regs.mono fun _ hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hr))

theorem crossClob_clob {s t : State} (h : Keeps VG.Proof.X448.AArch64.clob s t) : Keeps crossClob s t :=
  h.mono fun _ hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ hr))

theorem bnd_copy {m m' : Mem} {base : Addr} {o a : Nat} {n : Nat}
    (h : ∀ j < 8, limbs m' base o j = limbs m base a j) (hb : Bnd n m base a) : Bnd n m' base o := fun j hj => by
  rw [h j hj]; exact hb j hj

end VG.Proof.Ed448.AArch64.Window

end

end

/-! ### `Ed448.AArch64.Sparse.TableSetup`, which only this module used -/

section

/-! ### `Ed448.AArch64.Sparse.RestoreEntry`, which only this module used -/

section

/-! Restore entry zero to the accumulator after retaining its double in the key operand slots. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.X448.AArch64 (st)
open VG.Proof.X448.AArch64 (Scr Keeps Outside off ofs word write8_eq read8_eq word_write_aligned)
def restoreDst (w:Nat) : Nat := VG.Impl.X448.AArch64.slot (3+w/8)+8*(w%8)

private theorem restoreDst_bounds {w:Nat} (hw:w<24) :
    448≤restoreDst w ∧ restoreDst w+8≤832 ∧ restoreDst w%8=0 := by
  simp only [restoreDst,VG.Impl.X448.AArch64.slot]
  omega_using [hw]

def restoreSpan (n:Nat) : Nat := if n≤16 then 192 else 384

private theorem span_le (n:Nat) : restoreSpan n≤384 := by
  unfold restoreSpan
  split <;> omega_using []

private theorem restoreDst_span {n w:Nat} (hn:n≤24) (hw:w<n) :
    448≤restoreDst w ∧ restoreDst w+8≤448+restoreSpan n := by
  simp only [restoreSpan,restoreDst,VG.Impl.X448.AArch64.slot]
  split <;> omega_arith

def restoreWords (n a:Nat) : List Instr := (List.range n).flatMap fun w =>
  [.ldr .x .x4 .x3 (a+8*w),st .x4 (restoreDst w)]

private theorem restoreWord_ok {s:State} {base p:Addr} (hs:Scr s base)
    (hp:s.gpr .x3=p) {w a:Nat} (hw:w<24) (ha:a%8=0) (ha':a+8*w<32768)
    (hr:InRegions (s.rd++s.wr) (p+BitVec.ofNat 64 (a+8*w)) 8) :
    WP isa (.block [.ldr .x .x4 .x3 (a+8*w),st .x4 (restoreDst w)]) s fun t =>
      t.mem=s.mem.writeW (off base (restoreDst w)) (s.mem.readW (p+BitVec.ofNat 64 (a+8*w)) 64) ∧
      Keeps [.x4] s t := by
  have ep:p=base:=hp.symm.trans hs.x3
  rw [ep] at hr ⊢
  obtain ⟨_,hd,hd8⟩:=restoreDst_bounds hw
  have es:(a+8*w)%8=0 ∧ a+8*w<32768:=⟨by omega_using [ha],ha'⟩
  have ed:(restoreDst w)%8=0 ∧ restoreDst w<32768:=⟨hd8,by omega_using [hd]⟩
  have wr:=hs.write (d:=restoreDst w) (n:=8) (by omega_using [hd])
  apply WP.of_runBlock
  simp only [st,runBlock_cons,runStep_some,runBlock_nil,exec,addr,Size.bytes,es,ed,and_self,
    ite_true,hs.x3,State.read,Size.bits,BitVec.setWidth_eq,State.load,State.store,hr,wr,
    read8_eq,write8_eq,RegUpd.gpr_write,RegUpd.mem_write,RegUpd.rd_write,RegUpd.wr_write,
    ite_false,reduceCtorEq,Option.bind_some,Option.map_some,Option.some.injEq,exists_eq_left']
  refine ⟨by trivial,⟨fun r h => ?_,rfl,rfl⟩⟩
  simp only [List.mem_singleton] at h
  simp only [RegUpd.gpr_write,h,ite_false]

theorem restoreWords_ok {s:State} {base p:Addr} (hs:Scr s base) (hp:s.gpr .x3=p)
    {n a:Nat} (hn:n≤24) (ha:a%8=0) (ha':a+8*n≤32768)
    (hr:∀ w<n,InRegions (s.rd++s.wr) (p+BitVec.ofNat 64 (a+8*w)) 8)
    (hfar:∀ w<n,∀ j<8,832≤ofs base (p+BitVec.ofNat 64 (a+8*w)+BitVec.ofNat 64 j)) :
    WP isa (.block (restoreWords n a)) s fun t =>
      (∀ w<n,word t.mem base (restoreDst w)=s.mem.readW (p+BitVec.ofNat 64 (a+8*w)) 64) ∧
      Outside base 448 (restoreSpan n) s.mem t.mem ∧ Keeps [.x4] s t := by
  unfold restoreWords
  let inv:=fun k (t:State) =>
    (∀ w<k,word t.mem base (restoreDst w)=s.mem.readW (p+BitVec.ofNat 64 (a+8*w)) 64) ∧
    Outside base 448 (restoreSpan n) s.mem t.mem ∧ Keeps [.x4] s t
  refine wp_range_flatMap (M:=isa) (N:=n) inv (fun k t hk ⟨tv,fo,kt⟩ => ?_)
    n (Nat.le_refl _) s ⟨fun _ h => by omega,Outside.refl _ _ _ _,Keeps.refl _ _⟩
  have ht:=hs.of_keeps kt (by decide)
  refine WP.mono (restoreWord_ok ht ((kt.1 _ (by decide)).trans hp) (by omega_using [hn, hk]) ha (by omega_using [ha', hk])
    (by rw [kt.2.1,kt.2.2];exact hr k hk)) fun u ⟨um,ku⟩ => ?_
  obtain ⟨dlo,dhi,dal⟩:=restoreDst_bounds (show k<24 by omega_using [hn, hk])
  have hsval:t.mem.readW (p+BitVec.ofNat 64 (a+8*k)) 64=
      s.mem.readW (p+BitVec.ofNat 64 (a+8*k)) 64 := by
    apply Mem.readW_congr
    intro j hj
    exact fo _ (Or.inr (by have := span_le n;have := hfar k hk j hj;omega_arith))
  refine ⟨fun w hw => ?_,?_,kt.trans ku⟩
  · rw [um,hsval,word_write_aligned _ _ (d:=restoreDst k) (e:=restoreDst w) (by omega_using [dhi]) (by have := restoreDst_bounds (show w<24 by omega_using [hn, hk, hw]);omega_using [this])
      dal (restoreDst_bounds (by omega_using [hn, hk, hw])).2.2]
    by_cases he:w=k
    · subst w
      rw [ite_eq_left rfl]
    · have hne:restoreDst w≠restoreDst k := by
        simp only [restoreDst,VG.Impl.X448.AArch64.slot]
        omega_using [he]
      rw [ite_eq_right hne]
      exact tv w (by omega_using [hw, he])
  · rw [um]
    have dh:=restoreDst_span hn hk
    exact fo.trans ((VG.Proof.X448.AArch64.writeW_outside _ _ _ (by omega_using [dhi])).mono dh.1 dh.2)

end VG.Proof.Ed448.AArch64.Sparse

end

end


/-! Retain 2P as the addend and restore P as the odd table accumulator. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.X448.AArch64 (slot ACC)
open VG.Impl.Ed448.AArch64 (TAB)
open VG.Impl.Ed448.AArch64.Sparse
open VG.Proof.X448.AArch64 (Scr Keeps Outside Outside2 limbs word off)
open VG.Proof.X448.AArch64.Weak (Index)
open VG.Proof.X448.AArch64.Fast (BEnv)
open VG.Proof.X448.AArch64.Base (pt)
open VG.Proof.Ed448.AArch64.Window (TPt TBnd tw)
open VG.Spec.Ed448 (Point)
open VG.Proof.Curve448.AArch64.Fast (Mb)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

theorem tableStepSetup_ok {s:State} {base:Addr} {P:Point} (hs:Scr s base) (hb:BEnv s.mem base)
    (hz:∀ w<8,limbs s.mem base (slot (19:Index).val) w=0)
    (hp:pt (EV s.mem base) 3 4 5=VG.Proof.Ed448.double P)
    (ht:TPt s.mem base 0=P ∧ TBnd s.mem base 0)
    (hxb:∀ w<8,(tw s.mem base 0 w).toNat<Mb) :
    WP isa (.block tableStepSetup) s fun t =>
      OddInv t base P 1 t ∧ EV t.mem base 20=EV s.mem base 20 ∧
      Outside2 base 64 2816 ACC 1152 s.mem t.mem ∧
      Keeps (.x19::VG.Proof.X448.AArch64.Fast.fclob) s t := by
  have he:tableStepSetup=VG.Impl.Ed448.AArch64.Point56.copy3 6 3++
      (restoreWords 24 TAB++[.movz .x .x19 1 0]):=by rfl
  rw [he,WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.Window.copy3_ok hs 6 3 (by decide) (by decide) (by decide))
    fun a ⟨av,akeep,ao,ak⟩ => ?_
  have ha:=hs.of_keeps ak (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (restoreWords_ok ha ha.x3 (Nat.le_refl 24) (by decide) (by decide)
    (fun w hw => ha.read (by simp only [TAB];omega_arith))
    (fun w hw j hj => by
      rw [VG.Proof.X448.AArch64.ofs_off base (by simp only [TAB];omega_arith)]
      simp only [TAB]
      omega_arith)) fun b ⟨bv,bo,bk⟩ => ?_
  change Outside base 448 384 a.mem b.mem at bo
  have hb':Scr b base:=ha.of_keeps bk (by decide)
  refine WP.mono (VG.Proof.X448.AArch64.Weak.setCounter_ok b 1 (by decide))
    fun t ⟨t19,tg,tm,tr,twr⟩ => ?_
  have tk:Keeps [.x19] b t:=⟨fun r hr => tg r (by simpa only [List.mem_singleton] using hr),tr,twr⟩
  have hst:=hb'.of_keeps tk (by decide)
  have src:∀ w<24,tw a.mem base 0 w=tw s.mem base 0 w:=by
    intro w hw
    exact ao.word (Or.inr (by simp only [slot,TAB];omega_arith)) (by simp only [TAB];omega_arith)
  have dstWord:∀ w<24,word t.mem base (restoreDst w)=tw s.mem base 0 w:=by
    intro w hw
    rw [tm,bv w hw]
    exact src w hw
  have fieldKeep:∀ (i:Index), (i.val < 3 ∨ 6 ≤ i.val) → ∀ j<8,
      limbs t.mem base (slot i.val) j=limbs a.mem base (slot i.val) j:=by
    intro i hi j hj
    have := i.isLt
    rw [tm]
    exact bo.limbs (by simp only [slot];omega_arith) (by simp only [slot];omega_arith) (by omega_arith)
  have ab:BEnv a.mem base:=by
    intro i j hj
    by_cases hi:i.val < 6 ∨ 9 ≤ i.val
    · rw [akeep i hi j hj]
      exact hb i j hj
    · have hr:slot i.val=slot (6+(i.val-6)):=by congr 1;omega_arith
      rw [hr,av _ (by omega_arith) j hj]
      exact hb ⟨3+(i.val-6),by omega_arith⟩ j hj
  have tb:BEnv t.mem base:=by
    intro i j hj
    by_cases hi:i.val < 3 ∨ 6 ≤ i.val
    · rw [fieldKeep i hi j hj]
      exact ab i j hj
    · have hr:restoreDst (8*(i.val-3)+j)=slot i.val+8*j:=by
        simp only [restoreDst,slot]
        omega_arith
      show (word t.mem base (slot i.val+8*j)).toNat<_
      rw [←hr,dstWord _ (by omega_arith)]
      exact ht.2 _ (by omega_arith)
  have cw:∀ c<3,∀ j<8,tw s.mem base 0 (8*c+j)=word t.mem base (slot (3+c)+8*j):=by
    intro c hc j hj
    rw [←dstWord _ (by omega_arith)]
    congr 1
    simp only [restoreDst,slot]
    omega_arith
  have envPt:pt (EV t.mem base) 3 4 5=P:=by
    rw [←ht.1]
    symm
    unfold TPt pt
    refine Point.mk.injEq _ _ _ _ _ _ |>.mpr ⟨?_,?_,?_⟩
    · exact Window.FV_entry _ _ _ (e:=0) (c:=0) (by omega_arith) (cw 0 (by decide))
    · exact Window.FV_entry _ _ _ (e:=0) (c:=1) (by omega_arith) (cw 1 (by decide))
    · exact Window.FV_entry _ _ _ (e:=0) (c:=2) (by omega_arith) (cw 2 (by decide))
  have cp:∀ c<3,∀ j<8,limbs t.mem base (slot (6+c)) j=limbs s.mem base (slot (3+c)) j:=by
    intro c hc j hj
    rw [fieldKeep ⟨6+c,by omega_arith⟩ (by change 6+c < 3 ∨ 6 ≤ 6+c;omega_arith) j hj]
    exact av c hc j hj
  have envPnt:pt (EV t.mem base) 6 7 8=VG.Proof.Ed448.double P:=by
    rw [←hp]
    unfold pt
    refine Point.mk.injEq _ _ _ _ _ _ |>.mpr ⟨?_,?_,?_⟩
    · exact Window.FV_of_limbs (cp 0 (by decide))
    · exact Window.FV_of_limbs (cp 1 (by decide))
    · exact Window.FV_of_limbs (cp 2 (by decide))
  have tz:∀ w<8,limbs t.mem base (slot (19:Index).val) w=0:=by
    intro w hw
    rw [fieldKeep _ (by decide) w hw,akeep _ (by decide) w hw]
    exact hz w hw
  have hOne:EV t.mem base 20=EV s.mem base 20:=by
    apply Window.FV_of_limbs
    intro j hj
    rw [fieldKeep _ (by decide) j hj,akeep _ (by decide) j hj]
  have ot:Outside2 base 64 2816 ACC 1152 s.mem t.mem:=by
    intro x hx _
    rw [tm,bo x (by omega_arith),ao x (by simp only [slot];omega_arith)]
  refine ⟨⟨⟨by decide,by decide⟩,hst,tb,tz,t19,?_,envPnt,rfl,?_,?_,rfl,rfl,rfl,fun _ _ _ _ => rfl⟩,
    hOne,ot,?_⟩
  · exact envPt
  · intro e he
    have he:e=0:=by omega_arith
    subst e
    refine ⟨?_,?_⟩
    · rw [Window.TPt_of_tw (fun w hw => by
        exact ot.word (Or.inr (by simp only [TAB];omega_arith)) (Or.inr (by simp only [ACC,TAB];omega_arith))
          (by simp only [TAB];omega_arith)),ht.1]
      rfl
    · intro w hw
      rw [tw,ot.word (Or.inr (by simp only [TAB];omega_arith)) (Or.inr (by simp only [ACC,TAB];omega_arith))
        (by simp only [TAB];omega_arith)]
      exact ht.2 w hw
  · intro e he w hw
    have he:e=0:=by omega_arith
    subst e
    have hm:tw t.mem base 0 w=tw s.mem base 0 w:=
      ot.word (Or.inr (by simp only [TAB];omega_arith)) (Or.inr (by simp only [ACC,TAB];omega_arith))
        (by simp only [TAB];omega_arith)
    rw [hm]
    exact hxb w hw
  · exact ((ak.mono (by decide)).trans (bk.mono (by decide))).trans (tk.mono (by decide))

end VG.Proof.Ed448.AArch64.Sparse

end

end

/-! Complete bounded odd-key table construction, retaining R for the cofactor check. -/

-- Formerly `VerifiedGarbage/Proof/Ed448/AArch64/Sparse/TableFields.lean`, which only this module imported.
section

/-! Initialize the odd table's first entry without changing the bounded representation. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.X448.AArch64 (slot ACC)
open VG.Impl.X448.AArch64.Base (constSlot limb)
open VG.Impl.Ed448.AArch64 (TAB tabStore)
open VG.Proof.X448.AArch64 (Scr Keeps Outside limbs)
open VG.Proof.X448.AArch64.Weak (Index)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd Same copyE FKeep)
open VG.Proof.X448.AArch64.Base (pt zero_env limb_lt)
open VG.Proof.Curve448.AArch64.Fast (Mb)
open VG.Proof.Ed448.AArch64.Window (slotPt TPt TBnd tabStore_ok tabStore_pt tabStore_bnd limb_zero)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

def tableFields : List Instr :=
  constSlot (slot 19) 0++constSlot (slot 20) 1++
  VG.Impl.Curve448.AArch64.copy (slot 3) (slot 6)++
  VG.Impl.Curve448.AArch64.copy (slot 4) (slot 7)++
  constSlot (slot 5) 1++[.movz .x .x19 0 0]++tabStore

structure FieldsOut (base:Addr) (s t:State) : Prop where
  scr : Scr t base
  env : BEnv t.mem base
  zero : ∀ w<8,limbs t.mem base (slot (19:Index).val) w=0
  zbound : Bnd Mb t.mem base (slot 5)
  counter : t.gpr .x19=0
  acc : pt (EV t.mem base) 3 4 5=slotPt s.mem base
  one : EV t.mem base 20=1
  tab : TPt t.mem base 0=slotPt s.mem base ∧ TBnd t.mem base 0
  xbound : Bnd Mb s.mem base (slot 6) → ∀ w<8,(Window.tw t.mem base 0 w).toNat<Mb
  keep : Keeps (.x19::VG.Proof.X448.AArch64.Fast.fclob) s t
  mem : OddFrame base s.mem t.mem

theorem tableFields_ok {s:State} {base:Addr} (hs:Scr s base) (hb:BEnv s.mem base) :
    WP isa (.block tableFields) s (FieldsOut base s) := by
  simp only [tableFields,List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (constE hs hb 19 0) fun a ⟨ab,asm,ae,av,ao,ak⟩ => ?_
  have ha:=hs.of_keeps ak (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constE ha ab 20 1) fun b ⟨bb,bsm,be,bv,bo,bk⟩ => ?_
  have hb':=ha.of_keeps bk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copyE hb' bb 3 6) fun c ⟨ck,cb,cv,csm,ce⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (copyE (ck.scr hb') cb 4 7) fun d ⟨dk,db,_,dsm,de⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (constE (dk.scr (ck.scr hb')) db 5 1) fun e ⟨eb,esm,ee,ev,eo,ek⟩ => ?_
  have he:Scr e base:=((dk.scr (ck.scr hb')).of_keeps ek (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.Weak.setCounter_ok e 0 (by decide))
    fun f ⟨f19,fg,fm,fr,fw⟩ => ?_
  have fk:Keeps [.x19] e f:=⟨fun r hr => fg r (by simpa only [List.mem_singleton] using hr),fr,fw⟩
  have hf:=he.of_keeps fk (by decide)
  refine WP.mono (tabStore_ok hf (e:=0) (by decide) f19) fun t ⟨tv,fo,tk⟩ => ?_
  have envTF:EV t.mem base=EV f.mem base:=by
    funext i
    have hi:=i.isLt
    unfold VG.Proof.X448.AArch64.Weak.E VG.Proof.X448.AArch64.Weak.F
    exact congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr fun j hj =>
      fo.limbs (Or.inl (by simp only [slot,TAB];omega_using [])) (by simp only [slot];omega_using []) (by omega_using [hj]))
  have tB:BEnv t.mem base:=by
    intro i j hj
    have hi:=i.isLt
    rw [fo.limbs (Or.inl (by simp only [slot,TAB];omega_using [])) (by simp only [slot];omega_using []) (by omega_using [hj]),fm]
    exact eb i j hj
  have ez:∀ w<8,limbs e.mem base (slot (19:Index).val) w=0:=by
    intro w hw
    rw [esm 19 (by decide) w hw,dsm 19 (by decide) w hw,csm 19 (by decide) w hw,
      bsm 19 (by decide) w hw]
    change (VG.Proof.X448.AArch64.word a.mem base (slot (19:Index).val+8*w)).toNat=0
    rw [av w hw,limb_zero]
    rfl
  have ep:pt (EV e.mem base) 3 4 5=slotPt s.mem base:=by
    rw [ee,de,ce,be,ae]
    rfl
  have en:EV e.mem base 20=1:=by
    rw [ee,de,ce,be]
    rfl
  refine ⟨hf.of_keeps tk (by decide),tB,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro w hw
    rw [fo.limbs (Or.inl (by simp only [slot,TAB];omega_using [])) (by decide) (by omega_using [hw]),fm]
    exact ez w hw
  · intro w hw
    show (VG.Proof.X448.AArch64.word t.mem base (slot 5+8*w)).toNat<Mb
    rw [fo.word (Or.inl (by simp only [slot,TAB];omega_using [hw])) (by simp only [slot];omega_using [hw]),fm]
    change (VG.Proof.X448.AArch64.word e.mem base (slot (5:Index).val+8*w)).toNat<Mb
    rw [ev w hw]
    exact Nat.lt_of_lt_of_le (limb_lt 1 w) (by decide)
  · exact (tk.1 _ (by decide)).trans f19
  · rw [envTF,fm]
    exact ep
  · rw [envTF,fm]
    exact en
  · refine ⟨?_,?_⟩
    · rw [tabStore_pt tv,fm]
      exact ep
    · exact tabStore_bnd (by rw [fm];exact eb) tv
  · intro hx w hw
    rw [Window.tw,tv w (by omega_using [hw]),fm]
    have heq:Window.src w=slot 3+8*w:=by simp only [Window.src,slot];omega_using [hw]
    rw [heq]
    change limbs e.mem base (slot (3:Index).val) w<Mb
    rw [esm 3 (by decide) w hw,dsm 3 (by decide) w hw,cv w hw,
      bsm 6 (by decide) w hw,asm 6 (by decide) w hw]
    exact hx w hw
  · have k1:Keeps (.x19::VG.Proof.X448.AArch64.Fast.fclob) s b:=
      (ak.mono (by decide)).trans (bk.mono (by decide))
    have k2:Keeps (.x19::VG.Proof.X448.AArch64.Fast.fclob) b d:=
      (ck.regs.mono (by decide)).trans (dk.regs.mono (by decide))
    have k3:Keeps (.x19::VG.Proof.X448.AArch64.Fast.fclob) d f:=
      (ek.mono (by decide)).trans (fk.mono (by decide))
    exact ((k1.trans k2).trans k3).trans (tk.mono (by decide))
  · have fa:OddFrame base s.mem a.mem:=fun x hx _ _ => ao x (by simp only [slot] at hx ⊢;omega_using [hx])
    have fb:OddFrame base a.mem b.mem:=fun x hx _ _ => bo x (by simp only [slot] at hx ⊢;omega_using [hx])
    have fe:OddFrame base d.mem e.mem:=fun x hx _ _ => eo x (by simp only [slot] at hx ⊢;omega_using [hx])
    rw [fm] at fo
    exact (((fa.trans fb).trans (OddFrame.of_outside2 ck.mem)).trans
      (OddFrame.of_outside2 dk.mem)).trans (fe.trans (OddFrame.of_entry (by decide) fo))

end VG.Proof.Ed448.AArch64.Sparse
end

end

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64 (TAB RX RY CAN)
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.X448.AArch64 (slot ACC)
open VG.Proof.X448.AArch64 (Scr Keeps Outside Outside2 limbs word ofs)
open VG.Proof.X448.AArch64.Weak (Index)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd Same)
open VG.Proof.Ed448.AArch64.Window (slotPt TPt TBnd copyS_ok)
open VG.Proof.X448.AArch64.Base (pt zero_env)
open VG.Proof.Curve448.AArch64.Fast (Mb)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- The table build may write field slots, products, R's saves, and eight entries. -/
def TableFrame (base:Addr) (m m':Mem) : Prop :=
  ∀ x,(ofs base x<64 ∨ 2880≤ofs base x) →
    (ofs base x<ACC ∨ ACC+1152≤ofs base x) →
    (ofs base x<RX ∨ RX+128≤ofs base x) →
    (ofs base x<RY ∨ TAB+1536≤ofs base x) → m' x=m x

theorem OddFrame.word {base:Addr} {m m':Mem} (h:OddFrame base m m') {d:Nat}
    (h1:d+8≤64 ∨ 2880≤d) (h2:d+8≤ACC ∨ ACC+1152≤d)
    (h3:d+8≤TAB ∨ TAB+1536≤d) (hd:d+8≤8192) : word m' base d=word m base d := by
  apply Mem.readW_congr
  intro i hi
  exact h _ (by rw [VG.Proof.X448.AArch64.ofs_off base (by omega_using [hd, hi])];omega_using [h1, hi])
    (by rw [VG.Proof.X448.AArch64.ofs_off base (by omega_using [hd, hi])];omega_using [h2, hi])
    (by rw [VG.Proof.X448.AArch64.ofs_off base (by omega_using [hd, hi])];omega_using [h3, hi])

structure TableOut (s:State) (base:Addr) (t:State) : Prop where
  scr : Scr t base
  env : BEnv t.mem base
  zero : ∀ w<8,limbs t.mem base (slot (19:Index).val) w=0
  one : EV t.mem base 20=1
  tab : OddTabOk t.mem base (slotPt s.mem base) 8
  xbound : ∀ e<8,∀ w<8,(Window.tw t.mem base e w).toNat<Mb
  rx : ∀ w<8,limbs t.mem base RX w=limbs s.mem base (slot 8) w
  ry : ∀ w<8,limbs t.mem base RY w=limbs s.mem base (slot 9) w
  chk : t.gpr .x20=s.gpr .x20
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  mem : TableFrame base s.mem t.mem

theorem oddTable_ok {s:State} {base:Addr} (hs:Scr s base) (hb:BEnv s.mem base) (hx:Bnd Mb s.mem base (slot 6)) :
    WP isa oddTable s (TableOut s base) := by
  have hi:tableInit=VG.Impl.Curve448.AArch64.copy RX (slot 8)++
      (VG.Impl.Curve448.AArch64.copy RY (slot 9)++tableFields):=by
    simp only [tableInit,tableFields,List.append_assoc]
  unfold oddTable
  rw [WP.seq_iff,hi,WP.block_append_iff]
  refine WP.mono (copyS_ok hs (o:=RX) (a:=slot 8) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun a ⟨av,ao,ak⟩ => ?_
  have ha:=hs.of_keeps ak (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copyS_ok ha (o:=RY) (a:=slot 9) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun b ⟨bv,bo,bk⟩ => ?_
  have hb':=ha.of_keeps bk (by decide)
  have sb:∀ (i:Index),∀ j<8,limbs b.mem base (slot i.val) j=limbs s.mem base (slot i.val) j:=by
    intro i j hj
    have hi:=i.isLt
    rw [bo.limbs (Or.inl (by simp only [slot,RY,CAN];omega_using [])) (by simp only [slot];omega_using []) (by omega_using [hj]),
      ao.limbs (Or.inl (by simp only [slot,RX];omega_using [])) (by simp only [slot];omega_using []) (by omega_using [hj])]
  have bb:BEnv b.mem base:=by
    intro i j hj
    rw [sb i j hj]
    exact hb i j hj
  have be:EV b.mem base=EV s.mem base:=by
    funext i
    exact Window.FV_of_limbs (sb i)
  refine WP.mono (tableFields_ok hb' bb) fun c hc => ?_
  have hcp:slotPt b.mem base=slotPt s.mem base:=by unfold slotPt;rw [be]
  refine WP.seq (WP.mono (Point56.doubleCall_ok hc.scr hc.env hc.zbound)
    fun d ⟨dk,db,dsm,_,_,_,de,_⟩ => ?_)
  have dz:∀ w<8,limbs d.mem base (slot (19:Index).val) w=0:=fun w hw => by
    rw [dsm 19 (by decide) w hw]
    exact hc.zero w hw
  have dp:pt (EV d.mem base) 3 4 5=VG.Proof.Ed448.double (slotPt s.mem base):=by
    rw [de,Window.dblEnv_345,hc.one,Window.dblPt_eq,hc.acc,hcp]
  have dt:TPt d.mem base 0=slotPt s.mem base ∧ TBnd d.mem base 0:=by
    have hw:∀ w<24,Window.tw d.mem base 0 w=Window.tw c.mem base 0 w:=fun w hw =>
      dk.mem.word (Or.inr (by simp only [TAB];omega_using [])) (Or.inr (by simp only [ACC,TAB];omega_using []))
        (by simp only [TAB];omega_using [hw])
    refine ⟨?_,fun w hw' => ?_⟩
    · rw [Window.TPt_of_tw hw,hc.tab.1,hcp]
    · rw [hw w hw']
      exact hc.tab.2 w hw'
  have dx:∀ w<8,(Window.tw d.mem base 0 w).toNat<Mb:=by
    intro w hw
    have hm:Window.tw d.mem base 0 w=Window.tw c.mem base 0 w:=
      dk.mem.word (Or.inr (by simp only [TAB];omega_using [])) (Or.inr (by simp only [ACC,TAB];omega_using []))
        (by simp only [TAB];omega_using [hw])
    rw [hm]
    exact hc.xbound (fun j hj => by
      change limbs b.mem base (slot (6:Index).val) j<Mb
      rw [sb 6 j hj]
      exact hx j hj) w hw
  refine WP.seq (WP.mono (tableStepSetup_ok (dk.scr hc.scr) db dz dp dt dx)
    fun e ⟨ei,eo,em,ek⟩ => ?_)
  refine WP.mono (oddLoop_ok 7 e (by decide) (by decide) ei) fun t ht => ?_
  have ce:OddFrame base c.mem e.mem:=(OddFrame.of_outside2 dk.mem).trans (OddFrame.of_outside2 em)
  have ct:OddFrame base c.mem t.mem:=ce.trans ht.mem
  refine ⟨ht.scr,ht.env,ht.zero,?_,ht.tab,ht.xbound,?_,?_,?_,?_,?_,?_⟩
  · rw [ht.one,eo]
    rw [Same.env dsm (i:=20) (by decide)]
    exact hc.one
  · intro w hw
    show (word t.mem base (RX+8*w)).toNat=_
    rw [ct.word (Or.inr (by simp only [RX];omega_using [])) (Or.inr (by simp only [ACC,RX];omega_using []))
      (Or.inr (by simp only [TAB,RX];omega_using [])) (by simp only [RX];omega_using [hw]),
      hc.mem.word (Or.inr (by simp only [RX];omega_using [])) (Or.inr (by simp only [ACC,RX];omega_using []))
      (Or.inr (by simp only [TAB,RX];omega_using [])) (by simp only [RX];omega_using [hw])]
    change limbs b.mem base RX w=_
    rw [bo.limbs (Or.inr (by simp only [RY,CAN,RX];omega_using [])) (by simp only [RX];omega_using []) (by omega_using [hw])]
    exact av w hw
  · intro w hw
    show (word t.mem base (RY+8*w)).toNat=_
    rw [ct.word (Or.inr (by simp only [RY,CAN];omega_using [])) (Or.inr (by simp only [ACC,RY,CAN];omega_using []))
      (Or.inl (by simp only [TAB,RY,CAN];omega_using [hw])) (by simp only [RY,CAN];omega_using [hw]),
      hc.mem.word (Or.inr (by simp only [RY,CAN];omega_using [])) (Or.inr (by simp only [ACC,RY,CAN];omega_using []))
      (Or.inl (by simp only [TAB,RY,CAN];omega_using [hw])) (by simp only [RY,CAN];omega_using [hw])]
    change limbs b.mem base RY w=_
    rw [bv w hw,ao.limbs (Or.inl (by simp only [slot,RX];omega_using [])) (by decide) (by omega_using [hw])]
  · rw [ht.chk,ek.1 _ (by decide),dk.regs.1 _ (by decide),hc.keep.1 _ (by decide),
      bk.1 _ (by decide),ak.1 _ (by decide)]
  · rw [ht.rd,ek.2.1,dk.regs.2.1,hc.keep.2.1,bk.2.1,ak.2.1]
  · rw [ht.wr,ek.2.2,dk.regs.2.2,hc.keep.2.2,bk.2.2,ak.2.2]
  · intro x hx hy hz hr
    rw [ct x hx hy (by simp only [TAB,RY,CAN] at hr ⊢;omega_using [hr]),
      hc.mem x hx hy (by simp only [TAB,RY,CAN] at hr ⊢;omega_using [hr]),
      bo x (by simp only [TAB,RY,CAN] at hr ⊢;omega_using [hr]),ao x hz]

end VG.Proof.Ed448.AArch64.Sparse

end

end

/-! Bounded point arithmetic invariants and immutable sparse tables. -/

-- Formerly `VerifiedGarbage/Proof/Ed448/AArch64/Sparse/Frame.lean`, which only this module imported.
section

/-! Frames shared by every sparse multiplication round. Digits, table entries,
R, and the outer verifier's saved registers are outside these write regions. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ACC)
open VG.Proof.X448.AArch64 (Scr Keeps ofs word)
open VG.Proof.X448.AArch64.Fast (FKeep fclob)

abbrev pointClob : List Reg := .x30::fclob

def JointFrame (base:Addr) (m m':Mem) : Prop :=
  ∀ a,(ofs base a<64 ∨ 2880≤ofs base a) →
    (ofs base a<ACC ∨ ACC+1152≤ofs base a) →
    (ofs base a<GSAVE ∨ GSAVE+64≤ofs base a) → m' a=m a

structure PointKeep (base:Addr) (s t:State) : Prop where
  regs : Keeps pointClob s t
  mem : JointFrame base s.mem t.mem

theorem PointKeep.refl (base:Addr) (s:State) : PointKeep base s s:=
  ⟨Keeps.refl _ _,fun _ _ _ _ => rfl⟩

theorem PointKeep.trans {base:Addr} {s t u:State} (h:PointKeep base s t) (g:PointKeep base t u) :
    PointKeep base s u:=⟨h.regs.trans g.regs,fun x a b c => (g.mem x a b c).trans (h.mem x a b c)⟩

theorem PointKeep.scr {base:Addr} {s t:State} (h:PointKeep base s t) (hs:Scr s base) : Scr t base:=
  hs.of_keeps h.regs (by decide)

theorem PointKeep.of_field {base:Addr} {s t:State} (h:FKeep base s t) : PointKeep base s t:=
  ⟨h.regs.mono (by decide),fun x a b _ => h.mem x a b⟩

theorem PointKeep.of_call {base:Addr} {s t:State} (h:Point56.CKeep base s t) : PointKeep base s t:=
  ⟨h.regs,fun x a b _ => h.mem x a b⟩

theorem PointKeep.of_affine {base:Addr} {s t:State} (h:AffineKeep base s t) : PointKeep base s t:=
  ⟨h.regs.mono (by decide),h.mem⟩

theorem PointKeep.of_keeps {base:Addr} {s t:State} {rs:List Reg} (h:Keeps rs s t)
    (hm:t.mem=s.mem) (hr:∀ r∈rs,r∈pointClob) : PointKeep base s t:=
  ⟨h.mono hr,fun _ _ _ _ => by rw [hm]⟩

theorem JointFrame.word {base:Addr} {m m':Mem} (h:JointFrame base m m') {d:Nat}
    (h1:d+8≤64 ∨ 2880≤d) (h2:d+8≤ACC ∨ ACC+1152≤d)
    (h3:d+8≤GSAVE ∨ GSAVE+64≤d) (hd:d+8≤8192) : word m' base d=word m base d := by
  apply Mem.readW_congr
  intro i hi
  exact h _ (by rw [VG.Proof.X448.AArch64.ofs_off base (by omega_using [hd, hi])];omega_using [h1, hi])
    (by rw [VG.Proof.X448.AArch64.ofs_off base (by omega_using [hd, hi])];omega_using [h2, hi])
    (by rw [VG.Proof.X448.AArch64.ofs_off base (by omega_using [hd, hi])];omega_using [h3, hi])

theorem BaseTableAt.of_frame {base p:Addr} {s t:State} (ht:BaseTableAt s base p)
    (hrw:t.rd++t.wr=s.rd++s.wr) (h:JointFrame base s.mem t.mem) : BaseTableAt t base p:=by
  refine ⟨?_,ht.far,fun i hi => ?_⟩
  · rw [hrw]
    exact ht.read
  · rw [←ht.val i hi]
    apply Mem.readW_congr
    intro j hj
    have he:p+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 j=p+BitVec.ofNat 64 (8*i+j):=
      VG.Offset.add_add _ _ _
    rw [he]
    have hf:=ht.far (8*i+j) (by omega_using [hi, hj])
    exact h _ (Or.inr (by omega_using [hf])) (Or.inr (by simp only [ACC];omega_using [hf]))
      (Or.inr (by simp only [GSAVE];omega_using [hf]))

theorem JointFrame.keyDigit {base:Addr} {m m':Mem} (h:JointFrame base m m') {i:Nat} (hi:i<464) :
    m' (VG.Proof.X448.AArch64.off base (VG.Impl.X448.AArch64.BITS+i))=
      m (VG.Proof.X448.AArch64.off base (VG.Impl.X448.AArch64.BITS+i)):=by
  apply h
  all_goals rw [VG.Proof.X448.AArch64.ofs_off' base (by simp only [VG.Impl.X448.AArch64.BITS];omega_using [hi])]
  all_goals simp only [VG.Impl.X448.AArch64.BITS,ACC,GSAVE];omega_arith

theorem JointFrame.baseDigit {base:Addr} {m m':Mem} (h:JointFrame base m m') {i:Nat} (hi:i<464) :
    m' (VG.Proof.X448.AArch64.off base (VG.Impl.Ed448.AArch64.Sparse.SDIG+i))=
      m (VG.Proof.X448.AArch64.off base (VG.Impl.Ed448.AArch64.Sparse.SDIG+i)):=by
  apply h
  all_goals rw [VG.Proof.X448.AArch64.ofs_off' base (by simp only [VG.Impl.Ed448.AArch64.Sparse.SDIG];omega_using [hi])]
  all_goals simp only [VG.Impl.Ed448.AArch64.Sparse.SDIG,ACC,GSAVE];omega_arith

theorem PointKeep.keyDigit {base:Addr} {s t:State} (h:PointKeep base s t) {i:Nat} (hi:i<464) :
    t.mem (VG.Proof.X448.AArch64.off base (VG.Impl.X448.AArch64.BITS+i))=
      s.mem (VG.Proof.X448.AArch64.off base (VG.Impl.X448.AArch64.BITS+i)):=h.mem.keyDigit hi

theorem PointKeep.baseDigit {base:Addr} {s t:State} (h:PointKeep base s t) {i:Nat} (hi:i<464) :
    t.mem (VG.Proof.X448.AArch64.off base (VG.Impl.Ed448.AArch64.Sparse.SDIG+i))=
      s.mem (VG.Proof.X448.AArch64.off base (VG.Impl.Ed448.AArch64.Sparse.SDIG+i)):=h.mem.baseDigit hi

theorem PointKeep.baseTable {base p:Addr} {s t:State} (h:PointKeep base s t)
    (ht:BaseTableAt s base p) : BaseTableAt t base p:=
  ht.of_frame (by rw [h.regs.2.1,h.regs.2.2]) h.mem

theorem BaseTableAt.of_far {base p:Addr} {s t:State} (ht:BaseTableAt s base p)
    (hrw:t.rd++t.wr=s.rd++s.wr)
    (hm:∀ a,8192≤ofs base a → t.mem a=s.mem a) : BaseTableAt t base p:=by
  refine ⟨hrw ▸ ht.read,ht.far,fun i hi => ?_⟩
  rw [←ht.val i hi]
  apply Mem.readW_congr
  intro j hj
  have he:p+BitVec.ofNat 64 (8*i)+BitVec.ofNat 64 j=p+BitVec.ofNat 64 (8*i+j):=Offset.add_add _ _ _
  rw [he]
  exact hm _ (ht.far _ (by omega_using [hi, hj]))

end VG.Proof.Ed448.AArch64.Sparse
end

end

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.X448.AArch64 (slot ACC)
open VG.Impl.Ed448.AArch64 (TAB)
open VG.Proof.X448.AArch64 (Scr limbs word)
open VG.Proof.X448.AArch64.Weak (Index)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd Same)
open VG.Proof.Curve448.AArch64.Fast (Mb)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

structure Core (base:Addr) (s:State) : Prop where
  scr : Scr s base
  env : BEnv s.mem base
  zero : ∀ w<8,limbs s.mem base (slot (19:Index).val) w=0
  one : EV s.mem base 20=1
  zbound : Bnd Mb s.mem base (slot 5)

theorem Core.after {base:Addr} {s t:State} (h:Core base s) (k:PointKeep base s t)
    (hb:BEnv t.mem base) {os:List Index} (sm:Same base os s.mem t.mem)
    (h19:(19:Index)∉os) (h20:(20:Index)∉os) (hz:Bnd Mb t.mem base (slot 5)) : Core base t:=by
  refine ⟨k.scr h.scr,hb,fun w hw => ?_,?_,hz⟩
  · rw [sm 19 h19 w hw]
    exact h.zero w hw
  · rw [Same.env sm h20]
    exact h.one

theorem Core.unchanged {base:Addr} {s t:State} (h:Core base s) (k:PointKeep base s t)
    (hb:BEnv t.mem base) {os:List Index} (sm:Same base os s.mem t.mem)
    (h19:(19:Index)∉os) (h20:(20:Index)∉os) (h5:(5:Index)∉os) : Core base t:=
  h.after k hb sm h19 h20 (fun j hj => by
    change limbs t.mem base (slot (5:Index).val) j<Mb
    rw [sm 5 h5 j hj]
    exact h.zbound j hj)

theorem Core.of_keeps {base:Addr} {s t:State} (h:Core base s) (k:PointKeep base s t)
    (hm:t.mem=s.mem) : Core base t:=by
  refine ⟨k.scr h.scr,?_,?_,?_,?_⟩ <;> rw [hm]
  exacts [h.env,h.zero,h.one,h.zbound]

theorem Core.regsOnly {base:Addr} {s t:State} {rs:List Reg} (h:Core base s)
    (k:VG.Proof.X448.AArch64.Keeps rs s t) (hm:t.mem=s.mem) (hr:.x3∉rs ∧ .x12∉rs) : Core base t:=by
  refine ⟨h.scr.of_keeps k hr,?_,?_,?_,?_⟩ <;> rw [hm]
  exacts [h.env,h.zero,h.one,h.zbound]

theorem JointFrame.oddTable {base:Addr} {m m':Mem} {P:Spec.Ed448.Point}
    (k:JointFrame base m m') (ht:OddTabOk m base P 8) : OddTabOk m' base P 8:=by
  have hm:∀ e<8,∀ w<24,Window.tw m' base e w=Window.tw m base e w:=fun e he w hw =>
    k.word (Or.inr (by simp only [TAB];omega_using [])) (Or.inr (by simp only [ACC,TAB];omega_using []))
      (Or.inl (by simp only [TAB,GSAVE];omega_using [he, hw])) (by simp only [TAB];omega_using [he, hw])
  intro e he
  refine ⟨?_,fun w hw => ?_⟩
  · rw [Window.TPt_of_tw (hm e he)]
    exact (ht e he).1
  · rw [hm e he w hw]
    exact (ht e he).2 w hw

theorem JointFrame.xbounds {base:Addr} {m m':Mem} (k:JointFrame base m m')
    (hxb:∀ e<8,∀ w<8,(Window.tw m base e w).toNat<Mb) :
    ∀ e<8,∀ w<8,(Window.tw m' base e w).toNat<Mb:=by
  intro e he w hw
  rw [Window.tw,k.word (Or.inr (by simp only [TAB];omega_using [])) (Or.inr (by simp only [ACC,TAB];omega_using []))
    (Or.inl (by simp only [TAB,GSAVE];omega_using [he, hw])) (by simp only [TAB];omega_using [he, hw])]
  exact hxb e he w hw

theorem acc_of_same {base:Addr} {m m':Mem} {os:List Index} (h:Same base os m m')
    (h3:(3:Index)∉os) (h4:(4:Index)∉os) (h5:(5:Index)∉os) :
    VG.Proof.X448.AArch64.Base.pt (EV m' base) 3 4 5=
      VG.Proof.X448.AArch64.Base.pt (EV m base) 3 4 5:=by
  simp only [VG.Proof.X448.AArch64.Base.pt]
  rw [Same.env h h3,Same.env h h4,Same.env h h5]

theorem PointKeep.oddTable {base:Addr} {s t:State} {P:Spec.Ed448.Point}
    (k:PointKeep base s t) (ht:OddTabOk s.mem base P 8) : OddTabOk t.mem base P 8:=k.mem.oddTable ht

theorem PointKeep.xbounds {base:Addr} {s t:State} (k:PointKeep base s t)
    (hxb:∀ e<8,∀ w<8,(Window.tw s.mem base e w).toNat<Mb) :
    ∀ e<8,∀ w<8,(Window.tw t.mem base e w).toNat<Mb:=k.mem.xbounds hxb

end VG.Proof.Ed448.AArch64.Sparse

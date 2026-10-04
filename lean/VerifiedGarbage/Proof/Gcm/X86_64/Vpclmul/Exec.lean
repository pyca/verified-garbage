import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec
import VerifiedGarbage.Impl.Gcm.X86_64.Vpclmul
import VerifiedGarbage.Proof.Framework.X86_64.LaneSse
import VerifiedGarbage.Proof.Framework.X86_64.YFrame

/-!
# GHASH with VPCLMULQDQ: what the instruction groups compute, as bits

Untrusted: everything here is checked by Lean. What each group of lane-wise
instructions of `Impl.Gcm.X86_64.Vpclmul` does to the products of each lane
(`Pclmul.Prod`), each the instructions of `Pclmul/Exec.lean` lane by lane
(`WP.lanes`): a load and its products (`load_ok`, `ldacc_ok`), the reduction
of both lanes (`reduce_lanes`) and their sum (`combine_ok`). What they
compute in the field is in `Vpclmul/Ghash.lean`, which needs the algebra of
`Proof/Gcm/Poly.lean`; this module does not, so that proofs about where the
products go (such as the interleaved loops of `Proof/Gcm/X86_64/Stitch/`)
import it alone.
-/

namespace VG.Proof.Gcm.X86_64.Vpclmul

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod Only prod zero_ok acc_ok reduce_ok pxor72_ok ea_at)
open VG.Impl.Gcm.X86_64.Pclmul (at_ poly)
open VG.Impl.Gcm.X86_64.Vpclmul (preg preg16 zero acc reduce ld combine next)
open VG.Spec.Gcm (Block blockAt)

/-! ## Lane by lane -/

/-- `vinserti128`'s and `vextracti128`'s immediate 1 selects the upper lane. -/
theorem getLsbD_one8 : (1 : BitVec 8).getLsbD 0 = true := rfl

/-- A block of lane-wise instructions whose SSE block leaves each lane's
registers but `rs` alone leaves the vector registers but `rs` alone. -/
theorem yframe_of_lanes {rs : List XReg} {s s' : State} (hk : VKeep s s')
    (ho : ∀ l < 2, ∀ r, r ∉ rs → (s'.proj l).xmm r = (s.proj l).xmm r) : YFrame rs s s' :=
  ⟨hk.gpr, hk.mem, hk.rd, hk.wr, fun r hr l hl => by simpa using ho l hl r hr⟩

theorem zero_lanes (s : State) :
    WP isa (.block zero) s fun s' => (∀ l < 2, prod (s'.proj l) = Prod.zero) ∧
      YFrame [.xmm8, .xmm9, .xmm10] s s' ∧ VKeep s s' := by
  refine WP.mono (WP.lanes (ss := Impl.Gcm.X86_64.Pclmul.zero) rfl fun l _ => zero_ok (s.proj l))
    fun s' ⟨hk, hq⟩ => ⟨fun l hl => (hq l hl).1, yframe_of_lanes hk fun l hl r hr => (hq l hl).2.xmm r hr,
      hk⟩

/-- `pshufb xmm7, xmm0`. -/
theorem pshufb7_ok (t : State) :
    WP isa (.block [.xop (.bin .pshufb .xmm7 .xmm0)]) t fun t' =>
      t'.xmm .xmm7 = XBinOp.eval .pshufb (t.xmm .xmm7) (t.xmm .xmm0) ∧ Only [.xmm7] t t' := by
  apply WP.of_runBlock
  simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.setXmm, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [hr, ite_false]

/-- The SSE block of a load's lane-wise instructions. -/
def ldacc (first : Bool) (b : XReg) : List Instr :=
  [.xop (.bin .pshufb .xmm7 .xmm0)] ++ (if first then [.xop (.bin .pxor .xmm7 .xmm2)] else []) ++
    Impl.Gcm.X86_64.Pclmul.acc .xmm7 b

theorem ldacc_ok (first : Bool) (b : XReg) (t : State) (hb7 : b ≠ .xmm7) (hb8 : b ≠ .xmm8)
    (hb9 : b ≠ .xmm9) (hb10 : b ≠ .xmm10) (hb11 : b ≠ .xmm11) :
    WP isa (.block (ldacc first b)) t fun t' =>
      prod t' = (prod t).acc
        ((if first then t.xmm .xmm2 else 0) ^^^ XBinOp.eval .pshufb (t.xmm .xmm7) (t.xmm .xmm0))
        (t.xmm b) ∧
      Only [.xmm7, .xmm8, .xmm9, .xmm10, .xmm11] t t' := by
  rw [ldacc, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (pshufb7_ok t) fun t₁ ⟨e₁, o₁⟩ => ?_
  have hp₁ : prod t₁ = prod t := o₁.prod (by decide) (by decide) (by decide)
  have hb₁ : t₁.xmm b = t.xmm b := o₁.xmm b (by simp [hb7])
  have h2₁ : t₁.xmm .xmm2 = t.xmm .xmm2 := o₁.xmm _ (by decide)
  have fin : ∀ t₂, Only [.xmm7] t₁ t₂ → t₂.xmm .xmm7 =
      (if first then t.xmm .xmm2 else 0) ^^^ XBinOp.eval .pshufb (t.xmm .xmm7) (t.xmm .xmm0) →
      WP isa (.block (Impl.Gcm.X86_64.Pclmul.acc .xmm7 b)) t₂ fun t' =>
        prod t' = (prod t).acc
          ((if first then t.xmm .xmm2 else 0) ^^^ XBinOp.eval .pshufb (t.xmm .xmm7) (t.xmm .xmm0))
          (t.xmm b) ∧ Only [.xmm7, .xmm8, .xmm9, .xmm10, .xmm11] t t' := by
    intro t₂ o₂ e₂
    refine WP.mono (acc_ok .xmm7 b t₂ (by decide) (by decide) (by decide) (by decide) hb8 hb9 hb10 hb11)
      fun t' ⟨p', o'⟩ => ⟨?_, ?_⟩
    · rw [p', o₂.prod (by decide) (by decide) (by decide), hp₁, e₂, o₂.xmm b (by simp [hb7]), hb₁]
    · exact ((o₁.trans o₂).trans o').weaken fun r hr => by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with (h | h) | (h | h | h | h) <;> simp [h]
  cases first <;> simp only [Bool.false_eq_true, ↓reduceIte] at fin ⊢
  · exact WP.block_nil (fin t₁ ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩ (by rw [e₁]; simp))
  · refine WP.mono (pxor72_ok t₁) fun t₂ ⟨e₂, o₂⟩ => fin t₂ o₂ (by rw [e₂, e₁, h2₁])

theorem load256_lo (m : Mem) (a : Addr) : (m.readW a 256).extractLsb' 0 128 = m.readW a 128 := by
  have e := readW_extract m a (w := 256) (k := 0) (n := 16) (by decide)
  simpa using e

theorem load256_hi (m : Mem) (a : Addr) :
    (m.readW a 256).extractLsb' 128 128 = m.readW (a + BitVec.ofNat 64 16) 128 := by
  have e := readW_extract m a (w := 256) (k := 16) (n := 16) (by decide)
  simpa using e

/-- The lane-wise instructions of a load. -/
abbrev restV (k : Nat) (p : XReg) : List Instr :=
  [.vop (.vbin .vpshufb .l256 .xmm7 .xmm7 .xmm0)] ++
    (if k = 0 then [.vop (.vbin .vpxor .l256 .xmm7 .xmm7 .xmm2)] else []) ++ acc .xmm7 p

theorem ld_eq (k : Nat) (p : XReg) : ld k p = .vmovdquLoad .l256 .xmm7 (at_ .rdx (32 * k)) :: restV k p := by
  simp only [ld, restV, List.cons_append]

theorem lane_load {k : Nat} (hk : k < 4) :
    laneSseBlock (restV k (preg k)) = some (ldacc (decide (k = 0)) (preg k)) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem lane_load16 {k : Nat} (hk : k < 8) :
    laneSseBlock (restV k (preg16 k)) = some (ldacc (decide (k = 0)) (preg16 k)) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- A register of powers: none the loads write, nor the mask, the reduction
constant or `Y`. -/
abbrev PReg (p : XReg) : Prop :=
  p ≠ .xmm7 ∧ p ≠ .xmm8 ∧ p ≠ .xmm9 ∧ p ≠ .xmm10 ∧ p ≠ .xmm11 ∧ p ≠ .xmm0 ∧ p ≠ .xmm1 ∧ p ≠ .xmm2

theorem preg_ne {k : Nat} : PReg (preg k) := by
  unfold preg; split <;> decide

theorem preg16_ne {k : Nat} : PReg (preg16 k) := by
  unfold preg16; split <;> decide

/-- Blocks `2k` and `2k + 1` at `rdx + 32 k`, added to the lanes' products
with the powers in `p`. -/
theorem load_ok {k : Nat} {p : XReg} (hl : laneSseBlock (restV k p) = some (ldacc (decide (k = 0)) p))
    (hpr : PReg p) (s : State) (h0 : ∀ l < 2, s.lane .xmm0 l = revMask)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofInt 64 ((32 * k : Nat) : Int)) 32) :
    WP isa (.block (ld k p)) s fun s' =>
      (∀ l < 2, prod (s'.proj l) = (prod (s.proj l)).acc
        ((if k = 0 then s.lane .xmm2 l else 0) ^^^
          blockAt s.mem (s.gpr .rdx + BitVec.ofInt 64 ((32 * k : Nat) : Int) + BitVec.ofNat 64 (16 * l)))
        (s.lane p l)) ∧
      YFrame [.xmm7, .xmm8, .xmm9, .xmm10, .xmm11] s s' := by
  obtain ⟨n7, n8, n9, n10, n11, -, -, n2⟩ := hpr
  let a := s.gpr .rdx + BitVec.ofInt 64 ((32 * k : Nat) : Int)
  let v := s.mem.readW a 256
  let s₁ := s.setV .l256 .xmm7 (v.extractLsb' 0 128) (v.extractLsb' 128 128)
  rw [ld_eq, WP.block_cons_iff]
  refine ⟨s₁, by simp only [isa, exec, State.load256, ea_at, hin, ite_true, Option.map_some]; rfl, ?_⟩
  have l7 : ∀ l < 2, s₁.lane .xmm7 l = s.mem.readW (a + BitVec.ofNat 64 (16 * l)) 128 := fun l hl => by
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · simp [s₁, State.lane_setV256, v, load256_lo]
    · simp [s₁, State.lane_setV256, v, load256_hi]
  have keep : ∀ r, r ≠ .xmm7 → ∀ l < 2, s₁.lane r l = s.lane r l := fun r hr l _ => by
    simp [s₁, State.lane_setV256, hr]
  refine WP.mono (WP.lanes hl fun l _ => ldacc_ok _ p (s₁.proj l) n7 n8 n9 n10 n11)
    fun s' ⟨hk', hq⟩ => ⟨fun l hl => ?_, ?_⟩
  · rw [(hq l hl).1]
    have hp : prod (s₁.proj l) = prod (s.proj l) := by
      simp only [prod, State.proj_xmm, keep .xmm8 (by decide) l hl, keep .xmm9 (by decide) l hl,
        keep .xmm10 (by decide) l hl]
    simp only [hp, State.proj_xmm, keep _ n7 l hl, l7 l hl, keep .xmm0 (by decide) l hl, h0 l hl,
      keep .xmm2 (by decide) l hl]
    rw [← blockAt_eq]
    by_cases h : k = 0 <;> simp only [a, h, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true]
  · refine ⟨hk'.gpr, hk'.mem, hk'.rd, hk'.wr, fun r hr l hl => ?_⟩
    have := (hq l hl).2.xmm r hr
    simp only [State.proj_xmm] at this
    rw [this, keep r (fun h => hr (h ▸ List.mem_cons_self)) l hl]

/-- Each lane's product, reduced, into that lane of `ymm7`. -/
theorem reduce_lanes (s : State) (h1 : ∀ l < 2, s.lane .xmm1 l = poly) :
    WP isa (.block (reduce .xmm7)) s fun s' =>
      (∀ l < 2, s'.lane .xmm7 l = Pclmul.reduce (prod (s.proj l))) ∧
      YFrame [.xmm8, .xmm9, .xmm10, .xmm11, .xmm7] s s' := by
  refine WP.mono (WP.lanes (ss := Impl.Gcm.X86_64.Pclmul.reduce .xmm7) rfl fun l hl =>
      reduce_ok .xmm7 (s.proj l) (by decide) (by decide) (by decide) (by decide) (by simpa using h1 l hl))
    fun s' ⟨hk, hq⟩ => ⟨fun l hl => by simpa using (hq l hl).1,
      yframe_of_lanes hk fun l hl r hr => (hq l hl).2.xmm r hr⟩

/-- The two lanes' blocks added into `xmm2`, whose upper lane is cleared. -/
theorem combine_ok (s : State) :
    WP isa (.block combine) s
      fun s' => s'.lane .xmm2 0 = s.lane .xmm7 0 ^^^ s.lane .xmm7 1 ∧ s'.lane .xmm2 1 = 0 ∧
        YFrame [.xmm11, .xmm2] s s' := by
  rw [combine, WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  refine ⟨by simp [VBinOp.sse, Pclmul.eval_pxor, VOp.exec, State.setV, State.lane], by simp, by simp,
    by simp, by simp, by simp, fun r hr l hl => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
    simp [hr.1, hr.2, VOp.exec, State.setV, State.lane]

/-- The end of the eight-block body: `add rdx, 128`, `sub rcx, 8`, `cmp rcx, 8`. -/
theorem next_ok (s : State) :
    WP isa (.block next) s
      fun s' => s'.gpr .rdx = s.gpr .rdx + 128 ∧ s'.gpr .rcx = s.gpr .rcx - 8 ∧
        s'.cf = some (decide ((s.gpr .rcx - 8).toNat < 8)) ∧
        (∀ r, r ≠ .rdx → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ (∀ r l, s'.lane r l = s.lane r l) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e128 : BitVec.signExtend 64 (128 : BitVec 32) = 128 := by decide
  have e8 : BitVec.signExtend 64 (8 : BitVec 32) = 8 := by decide
  rw [next]
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e128, e8,
    Option.bind_some, Option.some.injEq, exists_eq_left', and_self]
  exact ⟨trivial, trivial, rfl, fun r h1 h2 => by simp only [h2, ↓reduceIte, h1], fun _ _ => rfl, trivial⟩

end VG.Proof.Gcm.X86_64.Vpclmul

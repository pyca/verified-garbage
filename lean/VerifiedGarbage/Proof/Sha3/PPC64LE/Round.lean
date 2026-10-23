module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Straight
public import VerifiedGarbage.Proof.Sha3.Compl
public import VerifiedGarbage.Impl.Sha3.PPC64LE
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Straight
meta import VerifiedGarbage.Proof.Sha3.Compl
meta import VerifiedGarbage.Impl.Sha3.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Keccak-f[1600] on PPC64LE: a round, by evaluation

As on x86-64 (`Proof/Sha3/X86_64/Round.lean`): a round (`round s d k`) is
checked by evaluating its code over the ANF domain (`Bitslice.Anf`, with
`Straight.eval`): the lanes of the state at `s`, as stored (complemented,
`Compl.cmpl`), are atoms `0–24`, row 4 of it is in `rowReg` on entry, and
`ONES` holds all ones (the constant `one`). ι's load of the round constant
(`8k(r19)`, a third memory area) splits the round in two: it loads atom 25
into `r0` and XORs it into `r11`. `check` then compares what the round
stores at `d`, and leaves in `rowReg`, with the round computed from the
specification (`Compl.specP`), and `round_ok` turns that into a statement
about the machine. The two rounds of an iteration (`check₀`, `check₁`) are
each checked once.

The prologue and the epilogue complement the lanes `complLanes` in place
(`complement`), which is checked the same way (`slots_ok`).
-/

@[expose] public section

namespace VG.Proof.Sha3.PPC64LE.Round

open VG VG.PPC64LE VG.PPC64LE.Straight VG.Bitslice.Anf VG.Impl.Sha3.PPC64LE
open VG.Proof.Sha3.Compl (specP)

/-- The registers of row 4 between rounds. -/
def rowReg (x : Nat) : Reg := [Reg.r5, .r6, .r7, .r8, .r9].getD x .r5

/-- The output state at `d` (slots), the input state at `s` (external words). -/
def cfg (s d : Reg) : Cfg := { base := d, slots := 25, ext := s, exts := 25 }

def ext (k : Nat) : Option Poly := some (atom k)

/-- On entry, row 4 of the input in `rowReg`, and all ones in `ONES`. -/
def env₀ : Straight.Env Poly :=
  { reg := fun r => if r = .r5 then some (atom 20) else if r = .r6 then some (atom 21)
      else if r = .r7 then some (atom 22) else if r = .r8 then some (atom 23)
      else if r = .r9 then some (atom 24) else if r = .r18 then some one else none
    slot := fun _ => none }

/-- The output, and row 4 of it in `rowReg`. -/
def post (e : Straight.Env Poly) : Bool :=
  (List.range 25).all (fun j => e.slot j == some (specP j)) &&
    (List.range 5).all fun x => e.reg (rowReg x) == some (specP (20 + x))

/-- The round from `s` to `d`, with ι (the round constant, atom 25, loaded into
`r0` and XORed into `r11`) between `roundA` and `roundB`. -/
def check (s d : Reg) : Bool :=
  match Straight.eval anf (cfg s d) ext (roundA s) env₀ with
  | none => false
  | some e₁ => match e₁.reg .r11 with
    | none => false
    | some a => Straight.check anf (cfg s d) ext (roundB s d)
        ((e₁.setReg .r0 (atom 25)).setReg .r11 (pxor a (atom 25))) post

theorem of_check {s d : Reg} (h : check s d = true) :
    ∃ e₁ a, Straight.eval anf (cfg s d) ext (roundA s) env₀ = some e₁ ∧ e₁.reg .r11 = some a ∧
      Straight.check anf (cfg s d) ext (roundB s d)
        ((e₁.setReg .r0 (atom 25)).setReg .r11 (pxor a (atom 25))) post = true := by
  unfold check at h
  split at h
  · cases h
  · rename_i e₁ he₁
    split at h
    · cases h
    · rename_i a ha
      exact ⟨e₁, a, he₁, ha, h⟩

/-- The registers a round keeps: the pointers, `ONES`, the loop's registers,
and the nonvolatile registers it does not use. -/
def kept : List Reg :=
  [.r3, .r4, .r18, .r19, .r20, .r2, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

/-- The round's instructions write none of `kept`. -/
def keeps (s d : Reg) : Bool :=
  (roundA s ++ roundB s d).all fun i => kept.all fun r => Straight.dst i != some r

theorem env₀_reg {r : Reg} {a : Poly} (h : env₀.reg r = some a) :
    (∃ x < 5, r = rowReg x ∧ a = atom (20 + x)) ∨ (r = .r18 ∧ a = one) := by
  simp only [env₀] at h
  cases r <;> simp at h <;> subst h
  · exact .inl ⟨0, by decide, rfl, rfl⟩
  · exact .inl ⟨1, by decide, rfl, rfl⟩
  · exact .inl ⟨2, by decide, rfl, rfl⟩
  · exact .inl ⟨3, by decide, rfl, rfl⟩
  · exact .inl ⟨4, by decide, rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩

open VG.Proof.Sha3 (Lanes laneAddr outState)
open VG.Proof.Sha3.Compl (cmpl msk maskP eval_specP)

abbrev KState := Spec.Sha3.State
abbrev Lane := Spec.Sha3.Lane

theorem cmpl_get (A : KState) {i : Nat} (hi : i < 25) : (cmpl A)[i] = A[i] ^^^ msk i := by
  simp [cmpl]

/-- A round from the state at `s` to the state at `d`: on lanes kept
complemented (`cmpl`), with row 4 in `rowReg` before and after. -/
theorem round_ok {sR dR : Reg} (hc : check sR dR = true) (hk : keeps sR dR = true)
    (hsk : sR ∈ kept) (hdk : dR ∈ kept) (k : Nat) (hk8 : 8 * k < 2 ^ 15 ∧ 8 * k % 4 = 0)
    {s : State} {A : KState} {rc : Lane} {src dst : Addr}
    (hs : s.gpr sR = src) (hd : s.gpr dR = dst) (hs0 : sR ≠ .r0) (hd0 : dR ≠ .r0)
    (he : Proof.Sha3.Env s.rd s.wr src dst (s.gpr .r19 + BitVec.ofNat 64 (8 * k)))
    (hA : Lanes s.mem src (cmpl A))
    (hrow : ∀ x (hx : x < 5), s.gpr (rowReg x) = (cmpl A)[20 + x])
    (hones : s.gpr .r18 = BitVec.allOnes 64)
    (hrc : s.mem.readW (s.gpr .r19 + BitVec.ofNat 64 (8 * k)) 64 = rc) :
    WP isa (.block (round sR dR k)) s fun s' =>
      Lanes s'.mem dst (cmpl (outState A rc)) ∧
      (∀ x (hx : x < 5), s'.gpr (rowReg x) = (cmpl (outState A rc))[20 + x]) ∧
      Frame [⟨dst, 200⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.lr = s.lr ∧ ∀ r ∈ kept, s'.gpr r = s.gpr r := by
  obtain ⟨e₁, a, he₁, ha, hchk⟩ := of_check hc
  obtain ⟨e₃, he₃, hpost⟩ := Straight.of_check _ _ _ hchk
  let V : Nat → Lane := fun i => if i = 25 then rc else s.mem.readW (wordAddr src i) 64
  have hV : ∀ i (hi : i < 25), V i = A[i] ^^^ msk i := fun i hi => by
    simp only [V, show i ≠ 25 by omega, ite_false]
    rw [← cmpl_get A hi]; exact hA i hi
  have hV25 : V 25 = rc := by simp [V]
  have hok : Ok (cfg sR dR) s :=
    { slotIn := fun j hj => by simp only [cfg] at hj ⊢; rw [hd]; exact he.dst_out j hj
      extIn := fun j hj => by simp only [cfg] at hj ⊢; rw [hs]; exact he.src_in j hj
      slots := by simp only [cfg]; decide
      sep := fun j hj i hi => by
        simp only [cfg] at hj hi ⊢; rw [hd, hs]
        exact Region.Disjoint.sep he.dst_src (Proof.Sha3.lane_contains dst hj)
          (Proof.Sha3.lane_contains src hi) }
  have hrel : Rel (AnfRel V) (cfg sR dR) ext env₀ s :=
    { reg := fun r a h => by
        rcases env₀_reg h with ⟨x, hx, rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp only [AnfRel, eval_atom, V, show 20 + x ≠ 25 by omega, ite_false]
          rw [hrow x hx]; exact hA _ (by omega)
        · simp only [AnfRel, eval_one, hones]
      slot := fun _ _ _ h => by cases h
      ext := fun j a hj h => by
        simp only [ext, Option.some.injEq] at h; subst h
        simp only [cfg] at hj ⊢
        simp only [AnfRel, eval_atom, V, show j ≠ 25 by omega, ite_false, hs] }
  obtain ⟨s₁, hs₁, p₁⟩ := Straight.run (anf_sound V) hok hrel he₁
  have hk' : ∀ r ∈ kept, (roundA sR).all (fun i => Straight.dst i != some r) = true ∧
      (roundB sR dR).all (fun i => Straight.dst i != some r) = true := fun r hr => by
    simp only [keeps, List.all_append, Bool.and_eq_true, List.all_eq_true] at hk
    exact ⟨List.all_eq_true.mpr fun i hi => hk.1 i hi r hr, List.all_eq_true.mpr fun i hi => hk.2 i hi r hr⟩
  have k₁ : ∀ r ∈ kept, s₁.gpr r = s.gpr r := fun r hr =>
    p₁.other r (by rw [(hk' r hr).1]; decide)
  -- ι
  have hrcp : s₁.gpr .r19 + BitVec.ofNat 64 (8 * k) = s.gpr .r19 + BitVec.ofNat 64 (8 * k) := by
    rw [k₁ .r19 (by decide)]
  have hrc₁ : s₁.mem.readW (s.gpr .r19 + BitVec.ofNat 64 (8 * k)) 64 = rc := by
    rw [p₁.frame.readW (Region.contains_self _ _) ?_ (by decide), hrc]
    simp only [slotRegion, cfg, List.mem_singleton, forall_eq, hd]
    exact he.dst_rc.symm
  have hin₁ : InRegions (s₁.rd ++ s₁.wr) (s.gpr .r19 + BitVec.ofNat 64 (8 * k)) 8 := by
    rw [p₁.rd, p₁.wr]; exact he.rc_in
  let s₂ := s₁.write .r0 rc
  let s₃ := s₂.write .r11 (s₂.gpr .r11 ^^^ s₂.gpr .r0)
  have hexec : runBlock isa (iota k) s₁ = some s₃ := by
    simp only [iota, runBlock_cons, runStep_some, runBlock_nil, isa,
      exec_load_d (show Reg.r19 ≠ .r0 by decide) hk8 (by rw [hrcp]; exact hin₁), hrcp, hrc₁, exec_logic]
    rfl
  have h11 : s₃.gpr .r11 = s₁.gpr .r11 ^^^ rc := by simp [s₃, s₂, State.write]
  have hr0 : AnfRel V (atom 25) rc := by simp only [AnfRel, eval_atom, hV25]
  have hr11 : AnfRel V (pxor a (atom 25)) (s₁.gpr .r11 ^^^ rc) := by
    simp only [AnfRel, eval_pxor, eval_atom, hV25]; rw [p₁.rel.reg _ _ ha]
  have hb₁ : ∀ r, r = Reg.r0 ∨ r = .r11 → r ≠ (cfg sR dR).base ∧ r ≠ (cfg sR dR).ext := by
    rintro r (rfl | rfl) <;> simp only [cfg] <;> refine ⟨fun h => ?_, fun h => ?_⟩ <;> subst h <;>
      simp_all [kept]
  have p₂ := post_write p₁.ok p₁.rel hr0 (hb₁ .r0 (.inl rfl)).1 (hb₁ .r0 (.inl rfl)).2
  have p₂' := post_write p₂.ok p₂.rel (v := s₂.gpr .r11 ^^^ s₂.gpr .r0) (by
      simp only [s₂, State.write, show Reg.r11 ≠ .r0 by decide, ite_false, ite_true]; exact hr11)
    (hb₁ .r11 (.inr rfl)).1 (hb₁ .r11 (.inr rfl)).2
  obtain ⟨s₄, hs₄, p₄⟩ := Straight.run (anf_sound V) p₂'.ok p₂'.rel he₃
  have hbase : s₄.gpr dR = dst := by
    have := p₄.base.trans (p₂'.base.trans (p₂.base.trans p₁.base))
    simp only [cfg] at this; rw [this, hd]
  unfold round
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, hs₁, WP.of_runBlock ⟨s₃, hexec, WP.of_runBlock ⟨s₄, hs₄, ?_⟩⟩⟩
  simp only [post, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hpost
  refine ⟨fun i hi => ?_, fun x hx => ?_, ?_, p₄.rd.trans (p₂'.rd.trans (p₂.rd.trans p₁.rd)),
    p₄.wr.trans (p₂'.wr.trans (p₂.wr.trans p₁.wr)), p₄.sp.trans (p₂'.sp.trans (p₂.sp.trans p₁.sp)),
    p₄.lr.trans (p₂'.lr.trans (p₂.lr.trans p₁.lr)), fun r hr => ?_⟩
  · have h := p₄.rel.slot i _ (by simp only [cfg]; exact hi) (hpost.1 i hi)
    simp only [AnfRel, eval_specP hV hV25 hi, cfg, hbase] at h
    exact h.symm
  · have h := p₄.rel.reg _ _ (hpost.2 x hx)
    simp only [AnfRel, eval_specP hV hV25 (show 20 + x < 25 by omega)] at h
    exact h.symm
  · have f₁ := p₁.frame
    have f₄ := p₄.frame
    have hb₂ : s₃.gpr dR = dst := by
      have := p₂'.base.trans (p₂.base.trans p₁.base); simp only [cfg] at this; rw [this, hd]
    simp only [slotRegion, cfg, hd] at f₁ f₄
    rw [hb₂] at f₄
    exact f₁.trans f₄
  · have h0 : r ≠ .r0 := fun h => by subst h; simp [kept] at hr
    have h11 : r ≠ .r11 := fun h => by subst h; simp [kept] at hr
    rw [p₄.other r (by rw [(hk' r hr).2]; decide), p₂'.other r h11, p₂.other r h0, k₁ r hr]

deriving instance Lean.ToExpr for Poly

/- `specP` reads the tables of `sD` and `sB`, so that the kernel evaluates each of their
values once, not once for each lane that uses it. -/
materialize_table Compl.sD 5
materialize_table Compl.sB 5 5
materialize_table specP 25

theorem check₀ : check .r3 .r4 = true := by lit_decide
theorem check₁ : check .r4 .r3 = true := by lit_decide
theorem keeps₀ : keeps .r3 .r4 = true := by decide +kernel
theorem keeps₁ : keeps .r4 .r3 = true := by decide +kernel

/-! ## Complementing the lanes -/

/-- The state at `r3` (slots). -/
def sCfg : Cfg := { base := .r3, slots := 25, ext := .r3, exts := 0 }

/-- Lane `i` of the state is atom `i`, and `ONES` holds all ones. -/
def sEnv : Straight.Env Poly :=
  { reg := fun r => if r = .r18 then some one else none, slot := fun i => some (atom i) }

/-- The lanes `complLanes` complemented. -/
def cPost (e : Straight.Env Poly) : Bool :=
  (List.range 25).all fun i => e.slot i == some (pxor (atom i) (maskP i))

/-- And row 4 of the result in `rowReg`. -/
def rPost (e : Straight.Env Poly) : Bool :=
  cPost e && (List.range 5).all fun x => e.reg (rowReg x) == some (pxor (atom (20 + x)) (maskP (20 + x)))

theorem complement_check : Straight.check anf sCfg (fun _ => none) complement sEnv cPost = true := by
  decide +kernel

theorem complementRow_check :
    Straight.check anf sCfg (fun _ => none) (complement ++ loadRow) sEnv rPost = true := by
  decide +kernel

theorem complement_writes : ∀ r ∈ kept, (complement ++ loadRow).all (fun i => Straight.dst i != some r) = true := by
  decide +kernel

theorem complement_writes' : ∀ r ∈ kept, complement.all (fun i => Straight.dst i != some r) = true := by
  decide +kernel

theorem eval_compl (M : KState) {i : Nat} (hi : i < 25) :
    Bitslice.Anf.eval (fun j => M[j]!) (pxor (atom i) (maskP i)) = (cmpl M)[i] := by
  rw [eval_pxor, eval_atom, Compl.eval_maskP, cmpl_get M hi, Proof.Sha3.getElem!_eq _ hi]

/-- A block that complements the lanes `complLanes` of the state at `r3`. -/
theorem slots_ok {is : List Instr} {post : Straight.Env Poly → Bool}
    (hchk : Straight.check anf sCfg (fun _ => none) is sEnv post = true) (hpost : ∀ e, post e = true → cPost e = true)
    (hw : ∀ r ∈ kept, is.all (fun i => Straight.dst i != some r) = true)
    {s : State} {st : Addr} {M : KState} (hr3 : s.gpr .r3 = st) (hst : (⟨st, 200⟩ : Region) ∈ s.wr)
    (hones : s.gpr .r18 = BitVec.allOnes 64) (hM : Lanes s.mem st M) :
    ∃ s' e', runBlock isa is s = some s' ∧ post e' = true ∧
      Rel (AnfRel fun i => M[i]!) sCfg (fun _ => none) e' s' ∧
      Lanes s'.mem st (cmpl M) ∧ Frame [⟨st, 200⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ s'.lr = s.lr ∧ ∀ r ∈ kept, s'.gpr r = s.gpr r := by
  obtain ⟨e', he', hp⟩ := Straight.of_check _ _ _ hchk
  have hok : Ok sCfg s := Ok.of_region hst (by simp [sCfg, hr3]) (by simp [sCfg]) (by decide) rfl
  have hrel : Rel (AnfRel fun i => M[i]!) sCfg (fun _ => none) sEnv s :=
    { reg := fun r a h => by
        simp only [sEnv] at h
        split at h
        · rename_i hr; subst hr; cases h
          simp only [AnfRel, eval_one, hones]
        · cases h
      slot := fun k a hk h => by
        simp only [sEnv, Option.some.injEq] at h; subst h
        simp only [sCfg] at hk ⊢
        simp only [AnfRel, eval_atom, hr3, Proof.Sha3.getElem!_eq _ hk]
        exact (hM k hk).symm
      ext := fun _ _ _ h => by cases h }
  obtain ⟨s', hs', p⟩ := Straight.run (anf_sound _) hok hrel he'
  have hc := hpost e' hp
  simp only [cPost, List.all_eq_true, List.mem_range, beq_iff_eq] at hc
  refine ⟨s', e', hs', hp, p.rel, fun i hi => ?_, ?_, p.rd, p.wr, p.sp, p.lr,
    fun r hr => p.other r (by rw [hw r hr]; decide)⟩
  · have hb : s'.gpr .r3 = st := p.base.trans hr3
    have h := p.rel.slot i _ (by simp only [sCfg]; exact hi) (hc i hi)
    simp only [AnfRel, eval_compl M hi, sCfg, hb] at h
    exact h.symm
  · have f := p.frame
    simp only [slotRegion, sCfg, hr3] at f
    exact f

theorem rows_of {e : Straight.Env Poly} {s : State} {M : KState}
    (hr : Rel (AnfRel fun i => M[i]!) sCfg (fun _ => none) e s) (hp : rPost e = true) :
    ∀ x (hx : x < 5), s.gpr (rowReg x) = (cmpl M)[20 + x] := by
  intro x hx
  simp only [rPost, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hp
  have h := hr.reg _ _ (hp.2 x hx)
  simp only [AnfRel, eval_compl M (show 20 + x < 25 by omega)] at h
  exact h.symm

theorem cmpl_cmpl (A : KState) : cmpl (cmpl A) = A := by
  apply Vector.ext; intro i hi
  rw [cmpl_get _ hi, cmpl_get _ hi, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

end VG.Proof.Sha3.PPC64LE.Round

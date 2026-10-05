import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Spill
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Sha3.Compl
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Impl.Sha3.X86_64
import VerifiedGarbage.Spec.Sha3.Contract
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha3.Scratch
import VerifiedGarbage.Proof.Sha3.Seed34
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Impl.Sha3.X86_64.Stream
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Straight

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.X86_64.Round`. -/
section

/-!
# Keccak-f[1600] on x86-64: a round, by evaluation

A round (`round s d k`) is checked by evaluating its code over the ANF
domain (`Bitslice.Anf`, with `Straight.eval`): the lanes of the state at
`s`, as stored (complemented, `Compl.cmpl`), are atoms `0–24`, and row 4 of
it is in `rowReg` on entry. The one instruction the evaluator does not
model, ι's load of the round constant (`[rsi + r15 + …]`, a third memory
area), splits the round in two: it XORs atom 25 into `r9`. `check` then
compares what the round stores at `d`, and leaves in `rowReg`, with the
round computed from the specification (`Compl.specP`), and `round_ok`
turns that into a statement about the machine. The two rounds of an
iteration (`check₀`, `check₁`) are each checked once.

The prologue and the epilogue complement the lanes `complLanes` in place
(`complement`), which is checked the same way (`slots_ok`).
-/

namespace VG.Proof.Sha3.X86_64.Round

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice.Anf VG.Impl.Sha3.X86_64
open VG.Proof.Sha3.Compl (specP)

/-- The registers of row 4 between rounds. -/
def rowReg (x : Nat) : Reg := [Reg.rax, .rbx, .rcx, .rdx, .rbp].getD x .rax

/-- The output state at `d` (slots), the input state at `s` (external words). -/
def cfg (s d : Reg) : Cfg := { base := d, slots := 25, ext := s, exts := 25 }

def ext (k : Nat) : Option VG.Bitslice.Anf.Poly := some (atom k)

/-- On entry, row 4 of the input in `rowReg`. -/
def env₀ : Straight.Env VG.Bitslice.Anf.Poly :=
  { reg := fun r => if r = .rax then some (atom 20) else if r = .rbx then some (atom 21)
      else if r = .rcx then some (atom 22) else if r = .rdx then some (atom 23)
      else if r = .rbp then some (atom 24) else none
    slot := fun _ => none }

/-- The output, and row 4 of it in `rowReg`. -/
def post (e : Straight.Env VG.Bitslice.Anf.Poly) : Bool :=
  (List.range 25).all (fun j => e.slot j == some (specP j)) &&
    (List.range 5).all fun x => e.reg (VG.Proof.Sha3.X86_64.Round.rowReg x) == some (specP (20 + x))

/-- The round from `s` to `d`, with ι (the round constant, atom 25, XORed
into `r9`) between `roundA` and `roundB`. -/
def check (s d : Reg) : Bool :=
  match Straight.eval anf (VG.Proof.Sha3.X86_64.Round.cfg s d) VG.Proof.Sha3.X86_64.Round.ext (roundA s) VG.Proof.Sha3.X86_64.Round.env₀ with
  | none => false
  | some e₁ => match e₁.reg .r9 with
    | none => false
    | some a => Straight.check anf (VG.Proof.Sha3.X86_64.Round.cfg s d) VG.Proof.Sha3.X86_64.Round.ext (roundB s d) (e₁.setReg .r9 (pxor a (atom 25))) VG.Proof.Sha3.X86_64.Round.post

theorem of_check {s d : Reg} (h : VG.Proof.Sha3.X86_64.Round.check s d = true) :
    ∃ e₁ a, Straight.eval anf (VG.Proof.Sha3.X86_64.Round.cfg s d) VG.Proof.Sha3.X86_64.Round.ext (roundA s) VG.Proof.Sha3.X86_64.Round.env₀ = some e₁ ∧ e₁.reg .r9 = some a ∧
      Straight.check anf (VG.Proof.Sha3.X86_64.Round.cfg s d) VG.Proof.Sha3.X86_64.Round.ext (roundB s d) (e₁.setReg .r9 (pxor a (atom 25))) VG.Proof.Sha3.X86_64.Round.post = true := by
  unfold VG.Proof.Sha3.X86_64.Round.check at h
  split at h
  · cases h
  · rename_i e₁ he₁
    split at h
    · cases h
    · rename_i a ha
      exact ⟨e₁, a, he₁, ha, h⟩

/-- The registers a round keeps. -/
def kept : List Reg := [.rdi, .rsi, .r15, .rsp]

/-- The round's instructions write none of `kept`. -/
def keeps (s d : Reg) : Bool :=
  (roundA s ++ roundB s d).all fun i => kept.all fun r => i.dst != some r

theorem env₀_reg {r : Reg} {a : VG.Bitslice.Anf.Poly} (h : env₀.reg r = some a) :
    ∃ x < 5, r = VG.Proof.Sha3.X86_64.Round.rowReg x ∧ a = atom (20 + x) := by
  simp only [VG.Proof.Sha3.X86_64.Round.env₀] at h
  cases r <;> simp at h <;> subst h
  · exact ⟨0, by decide, rfl, rfl⟩
  · exact ⟨2, by decide, rfl, rfl⟩
  · exact ⟨3, by decide, rfl, rfl⟩
  · exact ⟨1, by decide, rfl, rfl⟩
  · exact ⟨4, by decide, rfl, rfl⟩

open VG.Proof.Sha3 (Lanes laneAddr outState)
open VG.Proof.Sha3.Compl (cmpl msk maskP eval_specP)

abbrev KState := Spec.Sha3.State
abbrev Lane := Spec.Sha3.Lane

theorem cmpl_get (A : VG.Proof.Sha3.X86_64.Round.KState) {i : Nat} (hi : i < 25) : (cmpl A)[i] = A[i] ^^^ msk i := by
  simp [cmpl]

/-- A round from the state at `s` to the state at `d`: on lanes kept
complemented (`cmpl`), with row 4 in `rowReg` before and after. -/
theorem round_ok {sR dR : Reg} (hc : VG.Proof.Sha3.X86_64.Round.check sR dR = true) (hk : VG.Proof.Sha3.X86_64.Round.keeps sR dR = true)
    (hsk : sR ∈ VG.Proof.Sha3.X86_64.Round.kept) (hdk : dR ∈ VG.Proof.Sha3.X86_64.Round.kept) (k : Nat)
    {s : State} {A : VG.Proof.Sha3.X86_64.Round.KState} {rc : VG.Proof.Sha3.X86_64.Round.Lane} {src dst : Addr}
    (hs : s.gpr sR = src) (hd : s.gpr dR = dst)
    (he : Proof.Sha3.Env s.rd s.wr src dst (s.ea (rcOp k)))
    (hA : Lanes s.mem src (cmpl A))
    (hrow : ∀ x (hx : x < 5), s.gpr (VG.Proof.Sha3.X86_64.Round.rowReg x) = (cmpl A)[20 + x])
    (hrc : s.mem.readW (s.ea (rcOp k)) 64 = rc) :
    WP isa (.block (round sR dR k)) s fun s' =>
      Lanes s'.mem dst (cmpl (outState A rc)) ∧
      (∀ x (hx : x < 5), s'.gpr (VG.Proof.Sha3.X86_64.Round.rowReg x) = (cmpl (outState A rc))[20 + x]) ∧
      Frame [⟨dst, 200⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ r ∈ VG.Proof.Sha3.X86_64.Round.kept, s'.gpr r = s.gpr r := by
  obtain ⟨e₁, a, he₁, ha, hchk⟩ := VG.Proof.Sha3.X86_64.Round.of_check hc
  obtain ⟨e₃, he₃, hpost⟩ := Straight.of_check _ _ _ hchk
  let V : Nat → VG.Proof.Sha3.X86_64.Round.Lane := fun i => if i = 25 then rc else s.mem.readW (wordAddr src i) 64
  have hV : ∀ i (hi : i < 25), V i = A[i] ^^^ msk i := fun i hi => by
    simp only [V, show i ≠ 25 by omega, ite_false]
    rw [← VG.Proof.Sha3.X86_64.Round.cmpl_get A hi]; exact hA i hi
  have hV25 : V 25 = rc := by simp [V]
  have hok : Ok (VG.Proof.Sha3.X86_64.Round.cfg sR dR) s :=
    { slotIn := fun j hj => by simp only [VG.Proof.Sha3.X86_64.Round.cfg] at hj ⊢; rw [hd]; exact he.dst_out j hj
      extIn := fun j hj => by simp only [VG.Proof.Sha3.X86_64.Round.cfg] at hj ⊢; rw [hs]; exact he.src_in j hj
      slots := by simp only [VG.Proof.Sha3.X86_64.Round.cfg]; decide
      sep := fun j hj i hi => by
        simp only [VG.Proof.Sha3.X86_64.Round.cfg] at hj hi ⊢; rw [hd, hs]
        exact Region.Disjoint.sep he.dst_src (Proof.Sha3.lane_contains dst hj)
          (Proof.Sha3.lane_contains src hi) }
  have hrel : Rel (AnfRel V) (VG.Proof.Sha3.X86_64.Round.cfg sR dR) VG.Proof.Sha3.X86_64.Round.ext VG.Proof.Sha3.X86_64.Round.env₀ s :=
    { reg := fun r a h => by
        obtain ⟨x, hx, rfl, rfl⟩ := VG.Proof.Sha3.X86_64.Round.env₀_reg h
        simp only [AnfRel, eval_atom, V, show 20 + x ≠ 25 by omega, ite_false]
        rw [hrow x hx]; exact hA _ (by omega)
      slot := fun _ _ _ h => by cases h
      ext := fun j a hj h => by
        simp only [VG.Proof.Sha3.X86_64.Round.ext, Option.some.injEq] at h; subst h
        simp only [VG.Proof.Sha3.X86_64.Round.cfg] at hj ⊢
        simp only [AnfRel, eval_atom, V, show j ≠ 25 by omega, ite_false, hs] }
  obtain ⟨s₁, hs₁, p₁⟩ := Straight.run (anf_sound V) hok hrel he₁
  have hk' : ∀ r ∈ VG.Proof.Sha3.X86_64.Round.kept, (roundA sR).all (fun i => i.dst != some r) = true ∧
      (roundB sR dR).all (fun i => i.dst != some r) = true := fun r hr => by
    simp only [VG.Proof.Sha3.X86_64.Round.keeps, List.all_append, Bool.and_eq_true, List.all_eq_true] at hk
    exact ⟨List.all_eq_true.mpr fun i hi => hk.1 i hi r hr, List.all_eq_true.mpr fun i hi => hk.2 i hi r hr⟩
  have k₁ : ∀ r ∈ VG.Proof.Sha3.X86_64.Round.kept, s₁.gpr r = s.gpr r := fun r hr =>
    p₁.other r (by rw [(hk' r hr).1]; decide)
  -- ι
  have hea : s₁.ea (rcOp k) = s.ea (rcOp k) := by
    simp only [State.ea, rcOp, k₁ .rsi (by decide), k₁ .r15 (by decide)]
  have hrc₁ : s₁.mem.readW (s.ea (rcOp k)) 64 = rc := by
    rw [p₁.frame.readW (Region.contains_self _ _) ?_ (by decide), hrc]
    simp only [slotRegion, VG.Proof.Sha3.X86_64.Round.cfg, List.mem_singleton, forall_eq, hd]
    exact he.dst_rc.symm
  have hin₁ : InRegions (s₁.rd ++ s₁.wr) (s.ea (rcOp k)) 8 := by rw [p₁.rd, p₁.wr]; exact he.rc_in
  let v := s₁.gpr .r9 ^^^ rc
  have hexec : exec (iota k) s₁ =
      some ((arithFlags s₁ v false false).setReg .r9 v) := by
    simp [iota, exec, execAlu, VG.X86_64.readSrc, State.load64, hea, hin₁, hrc₁, v]
  have hr9 : AnfRel V (pxor a (atom 25)) v := by
    simp only [AnfRel, eval_pxor, eval_atom, hV25, v]; rw [p₁.rel.reg _ _ ha]
  have hb₁ : Reg.r9 ≠ (VG.Proof.Sha3.X86_64.Round.cfg sR dR).base := fun h => by
    simp only [VG.Proof.Sha3.X86_64.Round.cfg] at h; subst h; simp [VG.Proof.Sha3.X86_64.Round.kept] at hdk
  have hx₁ : Reg.r9 ≠ (VG.Proof.Sha3.X86_64.Round.cfg sR dR).ext := fun h => by
    simp only [VG.Proof.Sha3.X86_64.Round.cfg] at h; subst h; simp [VG.Proof.Sha3.X86_64.Round.kept] at hsk
  have p₂ := post_setReg p₁.ok p₁.rel hr9 hb₁ hx₁ (arithFlags s₁ v false false) ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨s₃, hs₃, p₃⟩ := Straight.run (anf_sound V) p₂.ok p₂.rel he₃
  have hbase : s₃.gpr dR = dst := by
    have := p₃.base.trans (p₂.base.trans p₁.base)
    simp only [VG.Proof.Sha3.X86_64.Round.cfg] at this; rw [this, hd]
  unfold round
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, hs₁, WP.block_cons_iff.mpr ⟨_, hexec, WP.of_runBlock ⟨s₃, hs₃, ?_⟩⟩⟩
  simp only [VG.Proof.Sha3.X86_64.Round.post, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hpost
  refine ⟨fun i hi => ?_, fun x hx => ?_, ?_, p₃.rd.trans (p₂.rd.trans p₁.rd),
    p₃.wr.trans (p₂.wr.trans p₁.wr), fun r hr => ?_⟩
  · have h := p₃.rel.slot i _ (by simp only [VG.Proof.Sha3.X86_64.Round.cfg]; exact hi) (hpost.1 i hi)
    simp only [AnfRel, eval_specP hV hV25 hi, VG.Proof.Sha3.X86_64.Round.cfg, hbase] at h
    exact h.symm
  · have h := p₃.rel.reg _ _ (hpost.2 x hx)
    simp only [AnfRel, eval_specP hV hV25 (show 20 + x < 25 by omega)] at h
    exact h.symm
  · have f₁ := p₁.frame
    have f₃ := p₃.frame
    have hb₂ : ((arithFlags s₁ v false false).setReg .r9 v).gpr dR = dst := by
      have := p₂.base.trans p₁.base; simp only [VG.Proof.Sha3.X86_64.Round.cfg] at this; rw [this, hd]
    simp only [slotRegion, VG.Proof.Sha3.X86_64.Round.cfg, hb₂, hd] at f₁ f₃
    exact f₁.trans f₃
  · rw [p₃.other r (by rw [(hk' r hr).2]; decide), p₂.other r (fun h => by subst h; simp [VG.Proof.Sha3.X86_64.Round.kept] at hr), k₁ r hr]

deriving instance Lean.ToExpr for VG.Bitslice.Anf.Poly

materialize_table specP 30

theorem check₀ : VG.Proof.Sha3.X86_64.Round.check .rdi .rsi = true := by lit_decide
theorem check₁ : VG.Proof.Sha3.X86_64.Round.check .rsi .rdi = true := by lit_decide
theorem keeps₀ : VG.Proof.Sha3.X86_64.Round.keeps .rdi .rsi = true := by decide +kernel
theorem keeps₁ : VG.Proof.Sha3.X86_64.Round.keeps .rsi .rdi = true := by decide +kernel

/-! ## Complementing the lanes -/

/-- The state at `rdi` (slots). -/
def sCfg : Cfg := { base := .rdi, slots := 25, ext := .rdi, exts := 0 }

/-- Lane `i` of the state is atom `i`. -/
def sEnv : Straight.Env VG.Bitslice.Anf.Poly := { reg := fun _ => none, slot := fun i => some (atom i) }

/-- The lanes `complLanes` complemented. -/
def cPost (e : Straight.Env VG.Bitslice.Anf.Poly) : Bool :=
  (List.range 25).all fun i => e.slot i == some (pxor (atom i) (maskP i))

/-- And row 4 of the result in `rowReg`. -/
def rPost (e : Straight.Env VG.Bitslice.Anf.Poly) : Bool :=
  VG.Proof.Sha3.X86_64.Round.cPost e && (List.range 5).all fun x => e.reg (VG.Proof.Sha3.X86_64.Round.rowReg x) == some (pxor (atom (20 + x)) (maskP (20 + x)))

theorem complement_check : Straight.check anf VG.Proof.Sha3.X86_64.Round.sCfg (fun _ => none) complement VG.Proof.Sha3.X86_64.Round.sEnv VG.Proof.Sha3.X86_64.Round.cPost = true := by
  decide +kernel

theorem complementRow_check :
    Straight.check anf VG.Proof.Sha3.X86_64.Round.sCfg (fun _ => none) (complement ++ loadRow) VG.Proof.Sha3.X86_64.Round.sEnv VG.Proof.Sha3.X86_64.Round.rPost = true := by
  decide +kernel

theorem complement_writes : ∀ r ∈ VG.Proof.Sha3.X86_64.Round.kept, (complement ++ loadRow).all (fun i => i.dst != some r) = true := by
  decide +kernel

theorem complement_writes' : ∀ r ∈ VG.Proof.Sha3.X86_64.Round.kept, complement.all (fun i => i.dst != some r) = true := by
  decide +kernel

theorem eval_compl (M : VG.Proof.Sha3.X86_64.Round.KState) {i : Nat} (hi : i < 25) :
    Bitslice.Anf.eval (fun j => M[j]!) (pxor (atom i) (maskP i)) = (cmpl M)[i] := by
  rw [eval_pxor, eval_atom, Compl.eval_maskP, VG.Proof.Sha3.X86_64.Round.cmpl_get M hi, Proof.Sha3.getElem!_eq _ hi]

/-- A block that complements the lanes `complLanes` of the state at `rdi`. -/
theorem slots_ok {is : List Instr} {post : Straight.Env VG.Bitslice.Anf.Poly → Bool}
    (hchk : Straight.check anf VG.Proof.Sha3.X86_64.Round.sCfg (fun _ => none) is VG.Proof.Sha3.X86_64.Round.sEnv post = true) (hpost : ∀ e, post e = true → VG.Proof.Sha3.X86_64.Round.cPost e = true)
    (hw : ∀ r ∈ VG.Proof.Sha3.X86_64.Round.kept, is.all (fun i => i.dst != some r) = true)
    {s : State} {st : Addr} {M : VG.Proof.Sha3.X86_64.Round.KState} (hdi : s.gpr .rdi = st) (hst : (⟨st, 200⟩ : Region) ∈ s.wr)
    (hM : Lanes s.mem st M) :
    ∃ s' e', runBlock isa is s = some s' ∧ post e' = true ∧
      Rel (AnfRel fun i => M[i]!) VG.Proof.Sha3.X86_64.Round.sCfg (fun _ => none) e' s' ∧
      Lanes s'.mem st (cmpl M) ∧ Frame [⟨st, 200⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ r ∈ VG.Proof.Sha3.X86_64.Round.kept, s'.gpr r = s.gpr r := by
  obtain ⟨e', he', hp⟩ := Straight.of_check _ _ _ hchk
  have hok : Ok VG.Proof.Sha3.X86_64.Round.sCfg s := Ok.of_region hst (by simp [VG.Proof.Sha3.X86_64.Round.sCfg, hdi]) (by simp [VG.Proof.Sha3.X86_64.Round.sCfg]) (by decide) rfl
  have hrel : Rel (AnfRel fun i => M[i]!) VG.Proof.Sha3.X86_64.Round.sCfg (fun _ => none) VG.Proof.Sha3.X86_64.Round.sEnv s :=
    { reg := fun _ _ h => by cases h
      slot := fun k a hk h => by
        simp only [VG.Proof.Sha3.X86_64.Round.sEnv, Option.some.injEq] at h; subst h
        simp only [VG.Proof.Sha3.X86_64.Round.sCfg] at hk ⊢
        simp only [AnfRel, eval_atom, hdi, Proof.Sha3.getElem!_eq _ hk]
        exact (hM k hk).symm
      ext := fun _ _ _ h => by cases h }
  obtain ⟨s', hs', p⟩ := Straight.run (anf_sound _) hok hrel he'
  have hc := hpost e' hp
  simp only [VG.Proof.Sha3.X86_64.Round.cPost, List.all_eq_true, List.mem_range, beq_iff_eq] at hc
  refine ⟨s', e', hs', hp, p.rel, fun i hi => ?_, ?_, p.rd, p.wr, fun r hr => p.other r (by rw [hw r hr]; decide)⟩
  · have hb : s'.gpr .rdi = st := p.base.trans hdi
    have h := p.rel.slot i _ (by simp only [VG.Proof.Sha3.X86_64.Round.sCfg]; exact hi) (hc i hi)
    simp only [AnfRel, VG.Proof.Sha3.X86_64.Round.eval_compl M hi, VG.Proof.Sha3.X86_64.Round.sCfg, hb] at h
    exact h.symm
  · have f := p.frame
    simp only [slotRegion, VG.Proof.Sha3.X86_64.Round.sCfg, hdi] at f
    exact f

theorem rows_of {e : Straight.Env VG.Bitslice.Anf.Poly} {s : State} {M : VG.Proof.Sha3.X86_64.Round.KState}
    (hr : Rel (AnfRel fun i => M[i]!) VG.Proof.Sha3.X86_64.Round.sCfg (fun _ => none) e s) (hp : VG.Proof.Sha3.X86_64.Round.rPost e = true) :
    ∀ x (hx : x < 5), s.gpr (VG.Proof.Sha3.X86_64.Round.rowReg x) = (cmpl M)[20 + x] := by
  intro x hx
  simp only [VG.Proof.Sha3.X86_64.Round.rPost, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hp
  have h := hr.reg _ _ (hp.2 x hx)
  simp only [AnfRel, VG.Proof.Sha3.X86_64.Round.eval_compl M (show 20 + x < 25 by omega)] at h
  exact h.symm

theorem cmpl_cmpl (A : VG.Proof.Sha3.X86_64.Round.KState) : cmpl (cmpl A) = A := by
  apply Vector.ext; intro i hi
  rw [VG.Proof.Sha3.X86_64.Round.cmpl_get _ hi, VG.Proof.Sha3.X86_64.Round.cmpl_get _ hi, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

end VG.Proof.Sha3.X86_64.Round

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.X86_64.Permute`. -/
section

section

section

/-!
# SHA-3 on x86-64: one instruction at a time

Weakest-precondition rules for the instruction forms the SHA-3 code uses,
exposing only what changes, so that proofs about a block stay small.
-/

namespace VG.Proof.Sha3.X86_64

open VG VG.X86_64

theorem ofInt_natCast (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

/-- `s'` is `s` with register `d` set to `v` (flags aside). -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 64) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Upd.setReg (s : State) (d : Reg) (v : BitVec 64) : VG.Proof.Sha3.X86_64.Upd s (s.setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h], rfl, rfl, rfl⟩

theorem Upd.withFlags (s : State) (cf o zf sf : Option Bool) (d : Reg) (v : BitVec 64) :
    VG.Proof.Sha3.X86_64.Upd s ((s.setFlags cf o zf sf).setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, State.setFlags, h], rfl, rfl, rfl⟩

theorem Upd.flags (s : State) {w : Nat} (d : Reg) (x : BitVec w) (c o : Bool) (v : BitVec 64) :
    VG.Proof.Sha3.X86_64.Upd s ((arithFlags s x c o).setReg d v) d v :=
  Upd.withFlags _ _ _ _ _ _ _

theorem Upd.trans {s₁ s₂ s₃ : State} {d : Reg} {v w : BitVec 64} (h₁ : VG.Proof.Sha3.X86_64.Upd s₁ s₂ d v)
    (h₂ : VG.Proof.Sha3.X86_64.Upd s₂ s₃ d w) : VG.Proof.Sha3.X86_64.Upd s₁ s₃ d w :=
  ⟨h₂.gpr, fun r h => (h₂.other r h).trans (h₁.other r h), h₂.mem.trans h₁.mem,
    h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_mov {d r : Reg} (k : ∀ s', VG.Proof.Sha3.X86_64.Upd s s' d (s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_movm {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', VG.Proof.Sha3.X86_64.Upd s s' d (s.mem.readW a 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem m) :: is)) s Q := by
  refine WP.cons (s' := s.setReg d (s.mem.readW a 64)) ?_ (k _ (Upd.setReg _ _ _))
  simp [exec, readSrc, State.load64, ha, hin]

theorem wp_movi64 {d : Reg} {v : BitVec 64} (k : ∀ s', VG.Proof.Sha3.X86_64.Upd s s' d v → WP isa (.block is) s' Q) :
    WP isa (.block (.movImm64 d v :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_xor {d r : Reg} (k : ∀ s', VG.Proof.Sha3.X86_64.Upd s s' d (s.gpr d ^^^ s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_and {d r : Reg} (k : ∀ s', VG.Proof.Sha3.X86_64.Upd s s' d (s.gpr d &&& s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_xori {d : Reg} {v : BitVec 32}
    (k : ∀ s', VG.Proof.Sha3.X86_64.Upd s s' d (s.gpr d ^^^ v.signExtend 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_xorm {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', VG.Proof.Sha3.X86_64.Upd s s' d (s.gpr d ^^^ s.mem.readW a 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.mem m) :: is)) s Q := by
  refine WP.cons (s' := (arithFlags s (s.gpr d ^^^ s.mem.readW a 64) false false).setReg d
    (s.gpr d ^^^ s.mem.readW a 64)) ?_ (k _ (Upd.flags _ _ _ _ _ _))
  simp [exec, execAlu, readSrc, State.load64, ha, hin]

theorem wp_ror {d : Reg} {n : Nat} (h₁ : 1 ≤ n) (h₂ : n ≤ 63)
    (k : ∀ s', VG.Proof.Sha3.X86_64.Upd s s' d ((s.gpr d).rotateRight n) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .ror d n :: is)) s Q := by
  have e : exec (.shift .ror d n) s = some ((s.setFlags (some ((s.gpr d).rotateRight n).msb)
      (if n = 1 then some (((s.gpr d).rotateRight n).msb ^^ ((s.gpr d).rotateRight n).getMsbD 1)
        else none) s.zf s.sf).setReg d ((s.gpr d).rotateRight n)) := by
    simp only [exec, execShift, h₁, h₂, and_self, ite_true]
  exact WP.cons e (k _ (Upd.withFlags _ _ _ _ _ _ _))

theorem wp_addi {d : Reg} {v : BitVec 32}
    (k : ∀ s', VG.Proof.Sha3.X86_64.Upd s s' d (s.gpr d + v.signExtend 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_cmp {d r : Reg}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.cf = some (decide ((s.gpr d).toNat < (s.gpr r).toNat)) →
      s'.zf = some (s.gpr d - s.gpr r == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ rfl rfl rfl rfl rfl rfl)

theorem wp_store {m : MemOp} {r : Reg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 8)
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem.writeW a (s.gpr r) → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.store m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr r) }) ?_ (k _ rfl rfl rfl rfl)
  simp [exec, State.store64, ha, hout]

theorem wp_mov32i {d : Reg} {v : BitVec 32}
    (k : ∀ s', VG.Proof.Sha3.X86_64.Upd s s' d (v.setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov32 d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_subi {d : Reg} {v : BitVec 32}
    (k : ∀ s', VG.Proof.Sha3.X86_64.Upd s s' d (s.gpr d - v.signExtend 64) →
      s'.zf = some (s.gpr d - v.signExtend 64 == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem wp_addi_zf {d : Reg} {v : BitVec 32}
    (k : ∀ s', VG.Proof.Sha3.X86_64.Upd s s' d (s.gpr d + v.signExtend 64) →
      s'.zf = some (s.gpr d + v.signExtend 64 == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem wp_test {d : Reg}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.zf = some (s.gpr d &&& s.gpr d == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .test d (.reg d) :: is)) s Q :=
  WP.cons rfl (k _ rfl rfl rfl rfl rfl)

theorem wp_movzx8 {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', VG.Proof.Sha3.X86_64.Upd s s' d ((s.mem a).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.movzx8 d m :: is)) s Q := by
  refine WP.cons (s' := s.setReg d ((s.mem a).setWidth 64)) ?_ (k _ (Upd.setReg _ _ _))
  simp [exec, State.load8, ha, hin]

theorem wp_store8 {m : MemOp} {r : Reg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem.writeW a ((s.gpr r).setWidth 8) → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.store8 m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr r).setWidth 8) }) ?_ (k _ rfl rfl rfl rfl)
  simp [exec, State.store8, ha, hout]

end

theorem wp_nil {s : State} {Q : State → Prop} (h : Q s) : WP isa (.block []) s Q := WP.block_nil h

end VG.Proof.Sha3.X86_64

end

/-!
# Keccak-f[1600] on x86-64: addresses

(A round is proven by evaluation, in `Round.lean`.)
-/

namespace VG.Proof.Sha3.X86_64

open VG VG.X86_64 VG.Impl.Sha3.X86_64

abbrev KState := Spec.Sha3.State
abbrev Lane := Spec.Sha3.Lane

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = s.gpr b + BitVec.ofNat 64 d := by
  simp only [State.ea, at_]; rw [VG.Proof.Sha3.X86_64.ofInt_natCast]

theorem ea_lane (s : State) (b : Reg) (i : Nat) :
    s.ea (lane b i) = s.gpr b + BitVec.ofNat 64 (8 * i) := VG.Proof.Sha3.X86_64.ea_at s b (8 * i)

end VG.Proof.Sha3.X86_64

end

/-!
# Keccak-f[1600] on x86-64: the whole function
-/

namespace VG.Proof.Sha3

open Spec.Sha3

open VG.X86_64 in
/-- X86-64 contract for `vg_keccak_f1600(state: *mut [u64; 25], scratch: *mut
[u64; 64])`: applies Keccak-f[1600] to the state at `state`.

The code may read and write `state` (200 bytes) and `scratch` (512 bytes,
whose contents on exit are unspecified). These may not overlap each other,
nor the return address on the stack. The pointers are public; the state is
secret. It returns with `rdi` and `rsi` as they were, which callers rely
on. -/
def permuteX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 200⟩
    let scratch : Region := ⟨s.gpr .rsi, 512⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ ret.Disjoint state ∧ ret.Disjoint scratch
  post s s' := stateAt s'.mem (s.gpr .rdi) = keccakF (stateAt s.mem (s.gpr .rdi)) ∧
    s'.gpr .rdi = s.gpr .rdi ∧ s'.gpr .rsi = s.gpr .rsi
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi

open VG.X86_64 in
/-- X86-64 contract for `vg_keccak_absorb(state = rdi, rate = rsi, pos = rdx,
data = rcx, len = r8, scratch = r9) -> rax`: absorbs `data` into the streaming
state (`Repr`) and returns the new position in the block.

The code may read `data`, read and write `state` (200 bytes) and `scratch`
(640 bytes), and store a return address in the 8 bytes below `rsp`, none of
which overlap each other or the return address. `rate` is one of `rates`,
and `pos < rate`. -/
def absorbX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 200⟩
    let data : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
    let scratch : Region := ⟨s.gpr .r9, 640⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch ∧
    (s.gpr .rsi).toNat ∈ rates ∧ (s.gpr .rdx).toNat < (s.gpr .rsi).toNat
  post s s' :=
    (∀ msg, Repr s.mem (s.gpr .rdi) (s.gpr .rsi).toNat msg →
      (s.gpr .rdx).toNat = msg.length % (s.gpr .rsi).toNat →
      Repr s'.mem (s.gpr .rdi) (s.gpr .rsi).toNat
        (msg ++ bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)) ∧
    (s'.gpr .rax).toNat = ((s.gpr .rdx).toNat + (s.gpr .r8).toNat) % (s.gpr .rsi).toNat
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp

open VG.X86_64 in
/-- X86-64 contract for `vg_keccak_pad(state = rdi, rate = rsi, pos = rdx,
suffix = rcx, scratch = r8)`: absorbs the padding (with the low byte of
`suffix`) into the streaming state.

The code may read and write `state` (200 bytes) and `scratch` (640 bytes),
and store a return address in the 8 bytes below `rsp`, none of which overlap
each other or the return address. `rate` is one of `rates`, and
`pos < rate`. -/
def padX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 200⟩
    let scratch : Region := ⟨s.gpr .r8, 640⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ ret.Disjoint state ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint scratch ∧
    (s.gpr .rsi).toNat ∈ rates ∧ (s.gpr .rdx).toNat < (s.gpr .rsi).toNat
  post s s' := ∀ msg, Repr s.mem (s.gpr .rdi) (s.gpr .rsi).toNat msg →
    (s.gpr .rdx).toNat = msg.length % (s.gpr .rsi).toNat →
    stateAt s'.mem (s.gpr .rdi) =
      absorb (s.gpr .rsi).toNat (pad (s.gpr .rsi).toNat ((s.gpr .rcx).setWidth 8) msg)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

open VG.X86_64 in
/-- X86-64 contract for `vg_keccak_squeeze(state = rdi, rate = rsi, pos = rdx,
out = rcx, outlen = r8, scratch = r9) -> rax`: writes `outlen` bytes of output
from byte `pos` on to `out`, and returns the position after them, leaving a
state from which the output continues.

The code may read and write `state` (200 bytes), `out` (`outlen` bytes) and
`scratch` (640 bytes), and store a return address in the 8 bytes below
`rsp`, none of which overlap each other or the return address. `rate` is
one of `rates`, and `pos ≤ rate`. -/
def squeezeX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 200⟩
    let out : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
    let scratch : Region := ⟨s.gpr .r9, 640⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (s.gpr .rsi).toNat ∈ rates ∧ (s.gpr .rdx).toNat ≤ (s.gpr .rsi).toNat
  post s s' :=
    bytesAt s'.mem (s.gpr .rcx) (s.gpr .r8).toNat =
      squeezeFrom (s.gpr .rsi).toNat (stateAt s.mem (s.gpr .rdi)) (s.gpr .rdx).toNat (s.gpr .r8).toNat ∧
    (s'.gpr .rax).toNat ≤ (s.gpr .rsi).toNat ∧
    ∀ d, squeezeFrom (s.gpr .rsi).toNat (stateAt s'.mem (s.gpr .rdi)) (s'.gpr .rax).toNat d =
      squeezeFrom (s.gpr .rsi).toNat (stateAt s.mem (s.gpr .rdi))
        ((s.gpr .rdx).toNat + (s.gpr .r8).toNat) d
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.Sha3

namespace VG.Proof.Sha3.X86_64

open VG VG.X86_64 VG.Impl.Sha3.X86_64
open VG.Spec.Sha3 (stateAt keccakF rnd RC)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .rdi
abbrev scr : Addr := s₀.gpr .rsi
abbrev stR : Region := ⟨VG.Proof.Sha3.X86_64.st s₀, 200⟩
abbrev scrR : Region := ⟨VG.Proof.Sha3.X86_64.scr s₀, 512⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev A₀ : VG.Proof.Sha3.X86_64.KState := stateAt s₀.mem (VG.Proof.Sha3.X86_64.st s₀)

/-- The state the rounds read from before round `r`, and the one they write. -/
def cur (r : Nat) : Addr := if r % 2 = 0 then VG.Proof.Sha3.X86_64.st s₀ else VG.Proof.Sha3.X86_64.scr s₀
def oth (r : Nat) : Addr := if r % 2 = 0 then VG.Proof.Sha3.X86_64.scr s₀ else VG.Proof.Sha3.X86_64.st s₀

/-- Scratch offset `d`. -/
abbrev off (d : Nat) : Addr := VG.Proof.Sha3.X86_64.scr s₀ + BitVec.ofNat 64 d

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [VG.Proof.Sha3.X86_64.stR s₀, VG.Proof.Sha3.X86_64.scrR s₀]
  st_scr : (VG.Proof.Sha3.X86_64.stR s₀).Disjoint (VG.Proof.Sha3.X86_64.scrR s₀)
  ret_st : (VG.Proof.Sha3.X86_64.retR s₀).Disjoint (VG.Proof.Sha3.X86_64.stR s₀)
  ret_scr : (VG.Proof.Sha3.X86_64.retR s₀).Disjoint (VG.Proof.Sha3.X86_64.scrR s₀)

theorem pre_of (s₀ : State) (h : Proof.Sha3.permuteX86_64.pre s₀) : VG.Proof.Sha3.X86_64.Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem cur_succ (s₀ : State) (r : Nat) : VG.Proof.Sha3.X86_64.cur s₀ (r + 1) = VG.Proof.Sha3.X86_64.oth s₀ r := by
  simp only [VG.Proof.Sha3.X86_64.cur, VG.Proof.Sha3.X86_64.oth]; split <;> split <;> first | rfl | omega

theorem oth_succ (s₀ : State) (r : Nat) : VG.Proof.Sha3.X86_64.oth s₀ (r + 1) = VG.Proof.Sha3.X86_64.cur s₀ r := by
  simp only [VG.Proof.Sha3.X86_64.cur, VG.Proof.Sha3.X86_64.oth]; split <;> split <;> first | rfl | omega

theorem cur_cases (s₀ : State) (r : Nat) :
    (VG.Proof.Sha3.X86_64.cur s₀ r = VG.Proof.Sha3.X86_64.st s₀ ∧ VG.Proof.Sha3.X86_64.oth s₀ r = VG.Proof.Sha3.X86_64.scr s₀) ∨ (VG.Proof.Sha3.X86_64.cur s₀ r = VG.Proof.Sha3.X86_64.scr s₀ ∧ VG.Proof.Sha3.X86_64.oth s₀ r = VG.Proof.Sha3.X86_64.st s₀) := by
  simp only [VG.Proof.Sha3.X86_64.cur, VG.Proof.Sha3.X86_64.oth]; split
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩

namespace Pre
variable {s₀ : State} (h : VG.Proof.Sha3.X86_64.Pre s₀)
include h

theorem in_wr {R : Region} (hR : R = VG.Proof.Sha3.X86_64.stR s₀ ∨ R = VG.Proof.Sha3.X86_64.scrR s₀) {a : Addr} {n : Nat}
    (hc : R.Contains a n) : InRegions s₀.wr a n := by
  rw [h.wr]; rcases hR with rfl | rfl
  · exact ⟨_, by simp, hc⟩
  · exact ⟨_, by simp, hc⟩

theorem in_all {a : Addr} {n : Nat} (hw : InRegions s₀.wr a n) : InRegions (s₀.rd ++ s₀.wr) a n := by
  rw [h.rd]; exact hw

theorem lane_in {p : Addr} (hp : p = VG.Proof.Sha3.X86_64.st s₀ ∨ p = VG.Proof.Sha3.X86_64.scr s₀) {i : Nat} (hi : i < 25) :
    InRegions s₀.wr (laneAddr p i) 8 := by
  rcases hp with rfl | rfl
  · exact h.in_wr (.inl rfl) (lane_contains _ hi)
  · exact h.in_wr (.inr rfl) (contains_offset (by omega) (by omega))

theorem off_in {d : Nat} (hd : d + 8 ≤ 512) : InRegions s₀.wr (VG.Proof.Sha3.X86_64.off s₀ d) 8 :=
  h.in_wr (.inr rfl) (contains_offset hd (by omega))

/-- The first 200 bytes of the scratch space are disjoint from the state. -/
theorem st_scr200 : (VG.Proof.Sha3.X86_64.stR s₀).Disjoint ⟨VG.Proof.Sha3.X86_64.scr s₀, 200⟩ :=
  h.st_scr.sub_right (Region.sub_prefix (by omega))

/-- The state and the second state are disjoint from every later scratch offset. -/
theorem region_off {p : Addr} (hp : p = VG.Proof.Sha3.X86_64.st s₀ ∨ p = VG.Proof.Sha3.X86_64.scr s₀) {d n : Nat} (hd : 200 ≤ d)
    (hn : d + n ≤ 512) : Region.Disjoint ⟨p, 200⟩ ⟨VG.Proof.Sha3.X86_64.off s₀ d, n⟩ := by
  rcases hp with rfl | rfl
  · exact h.st_scr.sub_right (sub_offset hn (by omega))
  · have := off_disjoint (VG.Proof.Sha3.X86_64.scr s₀) (a := 0) (n := 200) (b := d) (k := n) (by omega) (by omega)
      (.inl hd)
    rwa [add_zero'] at this

theorem env (r : Nat) (hr : r < 24) :
    Env s₀.rd s₀.wr (VG.Proof.Sha3.X86_64.cur s₀ r) (VG.Proof.Sha3.X86_64.oth s₀ r) (VG.Proof.Sha3.X86_64.off s₀ (200 + 8 * r)) := by
  have hc := VG.Proof.Sha3.X86_64.cur_cases s₀ r
  have hcur : VG.Proof.Sha3.X86_64.cur s₀ r = VG.Proof.Sha3.X86_64.st s₀ ∨ VG.Proof.Sha3.X86_64.cur s₀ r = VG.Proof.Sha3.X86_64.scr s₀ := hc.imp (·.1) (·.1)
  have hoth : VG.Proof.Sha3.X86_64.oth s₀ r = VG.Proof.Sha3.X86_64.st s₀ ∨ VG.Proof.Sha3.X86_64.oth s₀ r = VG.Proof.Sha3.X86_64.scr s₀ := hc.symm.imp (·.2) (·.2)
  refine ⟨fun i hi => h.in_all (h.lane_in hcur hi), fun i hi => h.lane_in hoth hi,
    h.in_all (h.off_in (by omega)), ?_, h.region_off hoth (by omega) (by omega)⟩
  rcases hc with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ <;> rw [e₁, e₂]
  · exact h.st_scr200.symm
  · exact h.st_scr200

end Pre

/-! ## The scratch space -/

theorem saved_bound : ∀ p ∈ saved, 392 ≤ p.2 ∧ p.2 + 8 ≤ 440 := by decide

/-- The saved registers, and the round constants. -/
def Aux (s₀ : State) (m : Mem) : Prop :=
  Spill.Saved m (VG.Proof.Sha3.X86_64.scr s₀) s₀.gpr saved ∧ ∀ j < 24, m.readW (VG.Proof.Sha3.X86_64.off s₀ (200 + 8 * j)) 64 = RC j

/-- Writes outside the constants and the saved registers keep them. -/
theorem Aux.frame {s₀ : State} {m m' : Mem} (h : VG.Proof.Sha3.X86_64.Aux s₀ m) {R : Region}
    (hR : ∀ d, 200 ≤ d → d + 8 ≤ 440 → Region.Disjoint ⟨VG.Proof.Sha3.X86_64.off s₀ d, 8⟩ R) (hf : Frame [R] m m') :
    VG.Proof.Sha3.X86_64.Aux s₀ m' := by
  refine ⟨Spill.Saved.frame h.1 hf fun p hp r hr => ?_, fun j hj => ?_⟩
  · rw [List.mem_singleton.mp hr]
    have := VG.Proof.Sha3.X86_64.saved_bound p hp
    exact hR _ (by omega) (by omega)
  · rw [hf.readW (Region.contains_self _ _) (by simpa using hR _ (by omega) (by omega)) (by decide)]
    exact h.2 j hj

/-! ## The prologue -/

theorem setup_eq : setup = Spill.saveCode .rsi saved ++
    (List.range 24).flatMap (fun k =>
      ([.movImm64 .rax (RC k), .store (at_ .rsi (200 + 8 * k)) .rax] : List Instr)) ++
    ([.mov .r15 (.imm (-192))] : List Instr) := rfl

/-- During the stores of the round constants, from memory `m₁`. -/
def RcInv (s₀ : State) (m₁ : Mem) (k : Nat) (s : State) : Prop :=
  s.gpr .rdi = VG.Proof.Sha3.X86_64.st s₀ ∧ s.gpr .rsi = VG.Proof.Sha3.X86_64.scr s₀ ∧ s.gpr .rsp = s₀.gpr .rsp ∧
    s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ Frame [⟨VG.Proof.Sha3.X86_64.off s₀ 200, 192⟩] m₁ s.mem ∧
    ∀ j < k, s.mem.readW (VG.Proof.Sha3.X86_64.off s₀ (200 + 8 * j)) 64 = RC j

theorem rcs_ok {s₀ : State} (hp : VG.Proof.Sha3.X86_64.Pre s₀) (s : State) (hs : VG.Proof.Sha3.X86_64.RcInv s₀ s.mem 0 s) :
    WP isa (.block ((List.range 24).flatMap fun k =>
      [.movImm64 .rax (RC k), .store (at_ .rsi (200 + 8 * k)) .rax])) s (VG.Proof.Sha3.X86_64.RcInv s₀ s.mem 24) := by
  refine wp_range_flatMap (M := isa) (VG.Proof.Sha3.X86_64.RcInv s₀ s.mem) (fun k s hk ⟨hdi, hsi, hsp, hrd, hwr, hf, hv⟩ => ?_)
    24 (Nat.le_refl _) s hs
  refine VG.Proof.Sha3.X86_64.wp_movi64 fun s₁ h₁ => VG.Proof.Sha3.X86_64.wp_store (a := VG.Proof.Sha3.X86_64.off s₀ (200 + 8 * k))
    (by rw [VG.Proof.Sha3.X86_64.ea_at, h₁.other _ (by decide), hsi])
    (by rw [h₁.wr, hwr]; exact hp.off_in (by omega)) fun s' g' m' r' w' => VG.Proof.Sha3.X86_64.wp_nil ?_
  refine ⟨by rw [g', h₁.other _ (by decide), hdi], by rw [g', h₁.other _ (by decide), hsi],
    by rw [g', h₁.other _ (by decide), hsp], by rw [r', h₁.rd, hrd], by rw [w', h₁.wr, hwr], ?_,
    fun j hj => ?_⟩
  · rw [m', h₁.mem]
    refine hf.writeW (List.mem_singleton_self _) _ ?_
    rw [show VG.Proof.Sha3.X86_64.off s₀ (200 + 8 * k) = VG.Proof.Sha3.X86_64.off s₀ 200 + BitVec.ofNat 64 (8 * k) by
      simp only [VG.Proof.Sha3.X86_64.off]; rw [BitVec.ofNat_add]; ac_rfl]
    exact contains_offset (by omega) (by omega)
  · rw [m', h₁.mem, h₁.gpr]
    by_cases e : j = k
    · subst e; rw [Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_sep ?_ (by decide)]
      · exact hv j (by omega)
      · have := off_disjoint (VG.Proof.Sha3.X86_64.scr s₀) (a := 200 + 8 * j) (n := 8) (b := 200 + 8 * k) (k := 8)
          (by omega) (by omega) (by omega)
        exact this.sep (Region.contains_self _ _) (Region.contains_self _ _)

open VG.Proof.Sha3.X86_64.Round (rowReg kept round_ok check₀ check₁ keeps₀ keeps₁ slots_ok
  complement_check complementRow_check complement_writes complement_writes' rows_of cmpl_cmpl)
open VG.Proof.Sha3.Compl (cmpl)

/-- `r15` before iteration `j` of the loop. -/
def r15At (j : Nat) : BitVec 64 := BitVec.ofNat 64 (16 * j) - 192

/-- The rounds' invariant, before iteration `j` (round `2j`): the state,
with the lanes `complLanes` complemented, at `state`, and its row 4 in
`rowReg`. -/
structure LInv (s₀ : State) (j : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = VG.Proof.Sha3.X86_64.st s₀
  rsi : s.gpr .rsi = VG.Proof.Sha3.X86_64.scr s₀
  r15 : s.gpr .r15 = VG.Proof.Sha3.X86_64.r15At j
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  state : Lanes s.mem (VG.Proof.Sha3.X86_64.st s₀) (cmpl ((List.range (2 * j)).foldl rnd (VG.Proof.Sha3.X86_64.A₀ s₀)))
  row : ∀ x (hx : x < 5), s.gpr (VG.Proof.Sha3.X86_64.Round.rowReg x) = (cmpl ((List.range (2 * j)).foldl rnd (VG.Proof.Sha3.X86_64.A₀ s₀)))[20 + x]
  aux : VG.Proof.Sha3.X86_64.Aux s₀ s.mem
  frame : Frame [VG.Proof.Sha3.X86_64.stR s₀, VG.Proof.Sha3.X86_64.scrR s₀] s₀.mem s.mem

theorem lanes₀ (s₀ : State) : Lanes s₀.mem (VG.Proof.Sha3.X86_64.st s₀) (VG.Proof.Sha3.X86_64.A₀ s₀) := by
  intro i hi; simp [Spec.Sha3.stateAt, laneAddr]

theorem prologue_ok {s₀ : State} (hp : VG.Proof.Sha3.X86_64.Pre s₀) :
    WP isa (.block (setup ++ complement ++ loadRow)) s₀ (VG.Proof.Sha3.X86_64.LInv s₀ 0) := by
  rw [VG.Proof.Sha3.X86_64.setup_eq, List.append_assoc, List.append_assoc, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (Spill.save_ok .rsi saved s₀ fun p hp' => hp.off_in (by have := VG.Proof.Sha3.X86_64.saved_bound p hp'; omega))
    fun s₁ ⟨g₁, rd₁, wr₁, m₁⟩ => ?_
  have f₁ : Frame [⟨VG.Proof.Sha3.X86_64.off s₀ 392, 48⟩] s₀.mem s₁.mem := m₁ ▸ Spill.saveMem_frame _ _ _ _ fun p hp' => by
    have := VG.Proof.Sha3.X86_64.saved_bound p hp'; exact Offset.contains _ (by omega) (by omega) (by omega)
  have v₁ := m₁ ▸ Spill.saveMem_saved s₀.mem (VG.Proof.Sha3.X86_64.scr s₀) s₀.gpr saved (by decide)
  refine WP.mono (VG.Proof.Sha3.X86_64.rcs_ok hp s₁ ⟨by rw [g₁], by rw [g₁], by rw [g₁], rd₁, wr₁, Frame.refl _ _,
    fun _ h => absurd h (by omega)⟩) fun s₂ ⟨di₂, si₂, sp₂, rd₂, wr₂, f₂, v₂⟩ => ?_
  rw [List.singleton_append]
  refine WP.cons rfl ?_
  -- The prologue writes only scratch offsets 200 to 440 before complementing.
  have hf : Frame [⟨VG.Proof.Sha3.X86_64.off s₀ 200, 240⟩] s₀.mem s₂.mem := by
    refine (f₁.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_) <;>
      simp only [List.mem_singleton] at hr <;> subst hr <;>
      exact ⟨_, List.mem_singleton_self _, off_sub _ (by omega) (by omega) (by omega)⟩
  have hd₂ : Region.Disjoint (VG.Proof.Sha3.X86_64.stR s₀) ⟨VG.Proof.Sha3.X86_64.off s₀ 200, 240⟩ := hp.region_off (.inl rfl) (by omega) (by omega)
  have hA : Lanes s₂.mem (VG.Proof.Sha3.X86_64.st s₀) (VG.Proof.Sha3.X86_64.A₀ s₀) := fun i hi => by
    rw [hf.readW (lane_contains _ hi) (by simpa using hd₂) (by decide)]; exact VG.Proof.Sha3.X86_64.lanes₀ s₀ i hi
  have haux : VG.Proof.Sha3.X86_64.Aux s₀ s₂.mem := by
    refine ⟨Spill.Saved.frame v₁ f₂ fun p hp' r hr => ?_, v₂⟩
    rw [List.mem_singleton.mp hr]
    have := VG.Proof.Sha3.X86_64.saved_bound p hp'
    exact Offset.disjoint _ (by omega) (by omega) (by omega)
  let s₃ := s₂.setReg .r15 ((-192 : BitVec 32).signExtend 64)
  have hwr : (VG.Proof.Sha3.X86_64.stR s₀) ∈ s₃.wr := by
    show VG.Proof.Sha3.X86_64.stR s₀ ∈ s₂.wr; rw [wr₂, hp.wr]; simp
  obtain ⟨s₄, e₄, hs₄, hp₄, hr₄, hl₄, hf₄, rd₄, wr₄, k₄⟩ := VG.Proof.Sha3.X86_64.Round.slots_ok VG.Proof.Sha3.X86_64.Round.complementRow_check
    (fun e h => by simp only [Round.rPost, Bool.and_eq_true] at h; exact h.1) VG.Proof.Sha3.X86_64.Round.complement_writes
    (s := s₃) (show s₂.gpr .rdi = VG.Proof.Sha3.X86_64.st s₀ from di₂) hwr hA
  refine WP.of_runBlock ⟨s₄, hs₄, ?_⟩
  have hsk : Frame [VG.Proof.Sha3.X86_64.stR s₀, VG.Proof.Sha3.X86_64.scrR s₀] s₀.mem s₂.mem :=
    hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.Sha3.X86_64.scrR s₀, by simp, sub_offset (by omega) (by omega)⟩
  refine ⟨by rw [k₄ .rdi (by decide)]; exact di₂, by rw [k₄ .rsi (by decide)]; exact si₂,
    by rw [k₄ .r15 (by decide)]; rfl, by rw [k₄ .rsp (by decide)]; exact sp₂,
    by rw [rd₄]; exact rd₂, by rw [wr₄]; exact wr₂, by simpa using hl₄, fun x hx => ?_, ?_, ?_⟩
  · simpa using VG.Proof.Sha3.X86_64.Round.rows_of hr₄ hp₄ x hx
  · exact haux.frame (fun d hd hd' => (hp.region_off (.inl rfl) hd (by omega)).symm) hf₄
  · exact hsk.trans (hf₄.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.Sha3.X86_64.stR s₀, by simp, fun _ h => h⟩)

/-! ## The rounds -/

theorem r15At_succ : ∀ j < 12, VG.Proof.Sha3.X86_64.r15At j + BitVec.signExtend 64 (16 : BitVec 32) = VG.Proof.Sha3.X86_64.r15At (j + 1) := by
  decide

theorem r15At_zero : ∀ j < 12, (VG.Proof.Sha3.X86_64.r15At (j + 1) == 0) = decide (j + 1 = 12) := by decide

theorem rcOff : ∀ j < 12, ∀ k : Nat, k < 2 →
    VG.Proof.Sha3.X86_64.r15At j * BitVec.ofNat 64 1 + BitVec.ofInt 64 (392 + 8 * (k : Int)) = BitVec.ofNat 64 (200 + 8 * (2 * j + k)) := by
  decide

theorem ea_rcOp {s : State} {j k : Nat} (hj : j < 12) (hk : k < 2) {b : Addr} (hsi : s.gpr .rsi = b)
    (h15 : s.gpr .r15 = VG.Proof.Sha3.X86_64.r15At j) : s.ea (rcOp k) = b + BitVec.ofNat 64 (200 + 8 * (2 * j + k)) := by
  simp only [State.ea, rcOp, hsi, h15]
  rw [BitVec.add_assoc, VG.Proof.Sha3.X86_64.rcOff j hj k hk]

theorem cur_even (s₀ : State) (j : Nat) : VG.Proof.Sha3.X86_64.cur s₀ (2 * j) = VG.Proof.Sha3.X86_64.st s₀ ∧ VG.Proof.Sha3.X86_64.oth s₀ (2 * j) = VG.Proof.Sha3.X86_64.scr s₀ := by
  simp [VG.Proof.Sha3.X86_64.cur, VG.Proof.Sha3.X86_64.oth]

theorem cur_odd (s₀ : State) (j : Nat) : VG.Proof.Sha3.X86_64.cur s₀ (2 * j + 1) = VG.Proof.Sha3.X86_64.scr s₀ ∧ VG.Proof.Sha3.X86_64.oth s₀ (2 * j + 1) = VG.Proof.Sha3.X86_64.st s₀ := by
  simp [VG.Proof.Sha3.X86_64.cur, VG.Proof.Sha3.X86_64.oth, Nat.add_mod]

theorem foldl_two (A : VG.Proof.Sha3.X86_64.KState) (j : Nat) :
    (List.range (2 * (j + 1))).foldl rnd A = rnd (rnd ((List.range (2 * j)).foldl rnd A) (2 * j)) (2 * j + 1) := by
  rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega, foldl_succ, foldl_succ]

/-- Two rounds, from iteration `j`. -/
theorem body_ok {s₀ : State} (hp : VG.Proof.Sha3.X86_64.Pre s₀) {j : Nat} (hj : j < 12) {s : State} (hL : VG.Proof.Sha3.X86_64.LInv s₀ j s) :
    WP isa (.block body) s fun s' =>
      eval .ne s' = some (!decide (j + 1 = 12)) ∧ VG.Proof.Sha3.X86_64.LInv s₀ (j + 1) s' := by
  unfold body
  rw [WP.block_append_iff, WP.block_append_iff]
  have ⟨c₀, o₀⟩ := VG.Proof.Sha3.X86_64.cur_even s₀ j
  have ⟨c₁, o₁⟩ := VG.Proof.Sha3.X86_64.cur_odd s₀ j
  have he₀ := hp.env (2 * j) (by omega)
  have he₁ := hp.env (2 * j + 1) (by omega)
  rw [c₀, o₀] at he₀
  rw [c₁, o₁] at he₁
  have hea₀ := VG.Proof.Sha3.X86_64.ea_rcOp (k := 0) hj (by omega) hL.rsi hL.r15
  have hd₀ : Region.Disjoint ⟨VG.Proof.Sha3.X86_64.scr s₀, 200⟩ ⟨VG.Proof.Sha3.X86_64.off s₀ (200 + 8 * (2 * j + 1)), 8⟩ :=
    hp.region_off (.inr rfl) (by omega) (by omega)
  refine WP.mono (VG.Proof.Sha3.X86_64.Round.round_ok VG.Proof.Sha3.X86_64.Round.check₀ VG.Proof.Sha3.X86_64.Round.keeps₀ (by decide) (by decide) 0 (rc := RC (2 * j))
    (src := VG.Proof.Sha3.X86_64.st s₀) (dst := VG.Proof.Sha3.X86_64.scr s₀) hL.rdi hL.rsi
    (by rw [hL.rd, hL.wr, hea₀]; exact he₀) hL.state hL.row
    (by rw [hea₀]; exact hL.aux.2 (2 * j) (by omega))) fun s₁ ⟨l₁, w₁, f₁, rd₁, wr₁, k₁⟩ => ?_
  have aux₁ : VG.Proof.Sha3.X86_64.Aux s₀ s₁.mem := hL.aux.frame (fun d hd hd' => (hp.region_off (.inr rfl) hd (by omega)).symm) f₁
  have hea₁ := VG.Proof.Sha3.X86_64.ea_rcOp (k := 1) (b := VG.Proof.Sha3.X86_64.scr s₀) hj (by omega) (by rw [k₁ .rsi (by decide)]; exact hL.rsi)
    (by rw [k₁ .r15 (by decide)]; exact hL.r15)
  refine WP.mono (VG.Proof.Sha3.X86_64.Round.round_ok VG.Proof.Sha3.X86_64.Round.check₁ VG.Proof.Sha3.X86_64.Round.keeps₁ (by decide) (by decide) 1 (rc := RC (2 * j + 1))
    (src := VG.Proof.Sha3.X86_64.scr s₀) (dst := VG.Proof.Sha3.X86_64.st s₀)
    (by rw [k₁ .rsi (by decide)]; exact hL.rsi) (by rw [k₁ .rdi (by decide)]; exact hL.rdi)
    (by rw [rd₁, wr₁, hL.rd, hL.wr, hea₁]; exact he₁) l₁ w₁
    (by rw [hea₁]; exact aux₁.2 (2 * j + 1) (by omega))) fun s₂ ⟨l₂, w₂, f₂, rd₂, wr₂, k₂⟩ => ?_
  have h15 : s₂.gpr .r15 = VG.Proof.Sha3.X86_64.r15At j := by rw [k₂ .r15 (by decide), k₁ .r15 (by decide), hL.r15]
  refine VG.Proof.Sha3.X86_64.wp_addi_zf fun s₃ u₃ z₃ => VG.Proof.Sha3.X86_64.wp_nil ⟨?_, ?_⟩
  · simp only [eval, z₃, h15, VG.Proof.Sha3.X86_64.r15At_succ j hj, VG.Proof.Sha3.X86_64.r15At_zero j hj, Option.map_some]
  · have keep : ∀ r ∈ VG.Proof.Sha3.X86_64.Round.kept, r ≠ .r15 → s₃.gpr r = s.gpr r := fun r hr h => by
      rw [u₃.other r h, k₂ r hr, k₁ r hr]
    have hst : cmpl (Proof.Sha3.outState (Proof.Sha3.outState ((List.range (2 * j)).foldl rnd (VG.Proof.Sha3.X86_64.A₀ s₀))
        (RC (2 * j))) (RC (2 * j + 1))) = cmpl ((List.range (2 * (j + 1))).foldl rnd (VG.Proof.Sha3.X86_64.A₀ s₀)) := by
      rw [Proof.Sha3.outState_eq, Proof.Sha3.outState_eq, VG.Proof.Sha3.X86_64.foldl_two]
    rw [hst] at l₂ w₂
    have hrow : ∀ x < 5, VG.Proof.Sha3.X86_64.Round.rowReg x ≠ .r15 := by decide
    exact ⟨by rw [keep .rdi (by decide) (by decide), hL.rdi], by rw [keep .rsi (by decide) (by decide), hL.rsi],
      by rw [u₃.gpr, h15, VG.Proof.Sha3.X86_64.r15At_succ j hj], by rw [keep .rsp (by decide) (by decide), hL.rsp],
      by rw [u₃.rd, rd₂, rd₁, hL.rd], by rw [u₃.wr, wr₂, wr₁, hL.wr], by rw [u₃.mem]; exact l₂,
      fun x hx => by rw [u₃.other _ (hrow x hx), w₂ x hx],
      by rw [u₃.mem]; exact aux₁.frame (fun d hd hd' => (hp.region_off (.inl rfl) hd (by omega)).symm) f₂,
      by
        rw [u₃.mem]
        refine (hL.frame.trans (f₁.sub fun r hr => ?_)).trans (f₂.sub fun r hr => ?_) <;>
          simp only [List.mem_singleton] at hr <;> subst hr
        · exact ⟨VG.Proof.Sha3.X86_64.scrR s₀, by simp, Region.sub_prefix (by omega)⟩
        · exact ⟨VG.Proof.Sha3.X86_64.stR s₀, by simp, fun _ h => h⟩⟩

/-! ## The epilogue -/

/-- After the rounds and the complementing back. -/
structure EInv (s₀ s : State) : Prop where
  rdi : s.gpr .rdi = VG.Proof.Sha3.X86_64.st s₀
  rsi : s.gpr .rsi = VG.Proof.Sha3.X86_64.scr s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  state : Lanes s.mem (VG.Proof.Sha3.X86_64.st s₀) (keccakF (VG.Proof.Sha3.X86_64.A₀ s₀))
  aux : VG.Proof.Sha3.X86_64.Aux s₀ s.mem
  frame : Frame [VG.Proof.Sha3.X86_64.stR s₀, VG.Proof.Sha3.X86_64.scrR s₀] s₀.mem s.mem

theorem restore_ok {s₀ : State} (hp : VG.Proof.Sha3.X86_64.Pre s₀) {s : State} (hE : VG.Proof.Sha3.X86_64.EInv s₀ s) :
    WP isa (.block restore) s fun s' =>
      gprPreserved s₀ s' ∧ Proof.Sha3.permuteX86_64.post s₀ s' := by
  refine WP.mono (Spill.restore_ok .rsi saved s₀.gpr s (by decide) (fun p hp' => ?_)
    (by rw [hE.rsi]; exact hE.aux.1)) fun s' ⟨h₁, h₂, m, _⟩ => ?_
  · rw [hE.rsi, hE.rd, hE.wr]
    exact hp.in_all (hp.off_in (by have := VG.Proof.Sha3.X86_64.saved_bound p hp'; omega))
  refine ⟨⟨Spill.calleeSaved_ok h₁ h₂ (by decide) hE.rsp, ?_⟩, ?_, by rw [h₂ _ (by decide), hE.rdi],
    by rw [h₂ _ (by decide), hE.rsi]⟩
  · rw [m]
    exact hE.frame.readW (Region.contains_self _ _) (by simpa using ⟨hp.ret_st, hp.ret_scr⟩) (by decide)
  · apply Vector.ext
    intro i hi
    simp only [Spec.Sha3.stateAt, Vector.getElem_ofFn, m]
    exact hE.state i hi

theorem epilogue_ok {s₀ : State} (hp : VG.Proof.Sha3.X86_64.Pre s₀) {s : State} (hL : VG.Proof.Sha3.X86_64.LInv s₀ 12 s) :
    WP isa (.block (complement ++ restore)) s fun s' =>
      gprPreserved s₀ s' ∧ Proof.Sha3.permuteX86_64.post s₀ s' := by
  rw [WP.block_append_iff]
  have hwr : VG.Proof.Sha3.X86_64.stR s₀ ∈ s.wr := by rw [hL.wr, hp.wr]; simp
  obtain ⟨s₁, -, hs₁, -, -, hl₁, hf₁, rd₁, wr₁, k₁⟩ :=
    VG.Proof.Sha3.X86_64.Round.slots_ok VG.Proof.Sha3.X86_64.Round.complement_check (fun _ h => h) VG.Proof.Sha3.X86_64.Round.complement_writes' hL.rdi hwr hL.state
  refine WP.of_runBlock ⟨s₁, hs₁, VG.Proof.Sha3.X86_64.restore_ok hp ⟨by rw [k₁ .rdi (by decide), hL.rdi],
    by rw [k₁ .rsi (by decide), hL.rsi], by rw [k₁ .rsp (by decide), hL.rsp], by rw [rd₁, hL.rd],
    by rw [wr₁, hL.wr], ?_, ?_, ?_⟩⟩
  · rw [VG.Proof.Sha3.X86_64.Round.cmpl_cmpl] at hl₁; exact hl₁
  · exact hL.aux.frame (fun d hd hd' => (hp.region_off (.inl rfl) hd (by omega)).symm) hf₁
  · exact hL.frame.trans (hf₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.Sha3.X86_64.stR s₀, by simp, fun _ h => h⟩)

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : VG.Proof.Sha3.X86_64.Pre s₀) :
    WP isa permute s₀ fun s' => gprPreserved s₀ s' ∧ Proof.Sha3.permuteX86_64.post s₀ s' := by
  refine WP.seq (WP.mono (VG.Proof.Sha3.X86_64.prologue_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (Q := VG.Proof.Sha3.X86_64.LInv s₀ 12) ?_ fun s₂ h₂ => VG.Proof.Sha3.X86_64.epilogue_ok hp h₂)
  let Inv : Nat → State → Prop := fun n s => ∃ j, n = 12 - j ∧ j < 12 ∧ VG.Proof.Sha3.X86_64.LInv s₀ j s
  refine WP.loop (M := isa) Inv (fun n s ⟨j, hn, hj, hL⟩ => ?_) 12 s₁ ⟨0, rfl, by omega, h₁⟩
  refine WP.mono (VG.Proof.Sha3.X86_64.body_ok hp hj hL) fun s' ⟨he, hl⟩ => ?_
  by_cases hlast : j + 1 = 12
  · exact .inl ⟨by show eval .ne s' = _; rw [he, hlast]; rfl, hlast ▸ hl⟩
  · exact .inr ⟨by show eval .ne s' = _; rw [he]; simp [hlast], 12 - (j + 1), by omega, j + 1, rfl, by omega, hl⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 200⟩, ⟨0x2000, 512⟩]

theorem permute_correct (s : State) (hs : Proof.Sha3.permuteX86_64.pre s) :
    ∃ t s', Exec isa Impl.Sha3.X86_64.permute s t s' ∧ abiPreserved s s' ∧
      Proof.Sha3.permuteX86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := VG.Proof.Sha3.X86_64.correct (VG.Proof.Sha3.X86_64.pre_of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

/-- The constant-time analysis's taint without the round constants that the
prologue stores at `[200, 392)` of the scratch space: public, but no
address or branch depends on them, and the kernel checks the analysis much
faster without them (`taint_decide_weak`). -/
def dropRC (τ : VG.X86_64.Taint.T) : VG.X86_64.Taint.T :=
  { τ with slots := τ.slots.filter fun sl => !(200 ≤ sl.2.1 && sl.2.1 < 392) }

theorem permute_ct : ConstantTime isa Proof.Sha3.permuteX86_64.pre Proof.Sha3.permuteX86_64.pub
    Impl.Sha3.X86_64.permute := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi]) ?_ (by taint_decide_weak VG.Proof.Sha3.X86_64.dropRC)
  intro s₁ s₂ _ _ ⟨h1, h2⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> with_reducible assumption

theorem permute_verified :
    Verified X86_64.target Impl.Sha3.X86_64.permute (Spec.Sha3.permuteContract X86_64.abi) :=
  -- `permuteX86_64` also says that `rdi` and `rsi` are returned unchanged,
  -- which the shared contract leaves out.
  Verified.of_correct VG.Proof.Sha3.X86_64.permute_correct VG.Proof.Sha3.X86_64.permute_ct
    { pre := by
        sig_implies_pre [Spec.Sha3.permuteContract, Spec.Sha3.permuteSig,
          Proof.Sha3.permuteX86_64, X86_64.abi, X86_64.argRegs]
      post := by
        intro s s' _ h
        sig_eval [Spec.Sha3.permuteContract, Spec.Sha3.permuteSig, Proof.Sha3.permuteX86_64,
          X86_64.abi, X86_64.argRegs]
        exact h.1
      pub := by
        sig_implies_pub [Spec.Sha3.permuteContract, Spec.Sha3.permuteSig,
          Proof.Sha3.permuteX86_64, X86_64.abi, X86_64.argRegs]
      sat := by
        sig_implies_sat [Spec.Sha3.permuteContract, Spec.Sha3.permuteSig,
          Proof.Sha3.permuteX86_64, X86_64.abi, X86_64.argRegs]
          [Proof.Sha3.X86_64.satState] using Proof.Sha3.X86_64.satState }

end VG.Proof.Sha3.X86_64

section

/-!
# SHA-3 on x86-64: calling the permutation
-/

namespace VG.Proof.Sha3.X86_64

open VG VG.X86_64 VG.Impl.Sha3.X86_64
open VG.Spec.Sha3 (stateAt keccakF)

theorem permute_keeps : ((instrs permute).all fun i => !Taint.clobbers i .rsp) = true := by
  rw [← Code.allInstrs_eq]; decide +kernel

theorem permute_nosp : NoSp permute := by
  intro i hi
  simpa using List.all_eq_true.mp VG.Proof.Sha3.X86_64.permute_keeps i hi

theorem permute_depth : permute.depth = 0 := by decide +kernel

/-- A region disjoint from the return address of a call reads the same on
entry to the callee. -/
theorem callEntry_byte (s : State) {R : Region} (hd : (below (s.gpr .rsp) 8).Disjoint R)
    (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    s.callEntry.mem (R.base + BitVec.ofNat 64 i) = s.mem (R.base + BitVec.ofNat 64 i) :=
  Frame.bytes (rs := [below (s.gpr .rsp) 8])
    (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_call _ (by omega) (by omega)))
    (by simpa using hd.symm) hR hi

/-- Calling `vg_keccak_f1600` on the state at `rdi`, with scratch space at
`rsi`. -/
theorem call_ok {s : State} {st scr : Addr} (hdi : s.gpr .rdi = st) (hsi : s.gpr .rsi = scr)
    (d₁ : Region.Disjoint ⟨st, 200⟩ ⟨scr, 512⟩) (d₂ : (below (s.gpr .rsp) 8).Disjoint ⟨st, 200⟩)
    (d₃ : (below (s.gpr .rsp) 8).Disjoint ⟨scr, 512⟩)
    (hw : Covers [⟨st, 200⟩, ⟨scr, 512⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨st, 200⟩, ⟨scr, 512⟩, below (s.gpr .rsp) 8] s.mem s'.mem →
      stateAt s'.mem st = keccakF (stateAt s.mem st) →
      s'.gpr .rdi = st → s'.gpr .rsi = scr → Q s') :
    WP isa (.call "vg_keccak_f1600" permute) s Q := by
  have hne : ∀ r : Reg, r ≠ .rsp → s.callEntry.gpr r = s.gpr r := fun r h => State.callEntry_gpr _ h
  refine WP.call (k := Proof.Sha3.permuteX86_64) VG.Proof.Sha3.X86_64.permute_correct VG.Proof.Sha3.X86_64.permute_nosp
    (by rw [VG.Proof.Sha3.X86_64.permute_depth]; decide) (rd := []) (wr := [⟨st, 200⟩, ⟨scr, 512⟩]) ?_ ?_ hw ?_
  · simp only [Proof.Sha3.permuteX86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, hne _ (by decide : Reg.rdi ≠ .rsp),
      hne _ (by decide : Reg.rsi ≠ .rsp), hdi, hsi]
    exact ⟨trivial, trivial, d₁, d₂, d₃⟩
  · intro a n h
    obtain ⟨r, hr, hc⟩ := hw a n (by simpa using h)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost, hdi₂, hsi₂⟩
    simp only [State.withRegions_gpr, State.withRegions_mem, hne _ (by decide : Reg.rdi ≠ .rsp), hdi,
      hm₂] at hpost hdi₂
    simp only [State.withRegions_gpr, hne _ (by decide : Reg.rsi ≠ .rsp), hsi] at hsi₂
    have hst : stateAt s.callEntry.mem st = stateAt s.mem st :=
      Proof.Sha3.stateAt_congr fun i hi => VG.Proof.Sha3.X86_64.callEntry_byte s (R := ⟨st, 200⟩) d₂ (by simp) hi
    refine hQ s' hrd hwr hcs (by rw [VG.Proof.Sha3.X86_64.permute_depth] at hf; simpa using hf) (by rw [hpost, hst])
      (by rw [← hg₂ _ (by decide), hdi₂]) (by rw [← hg₂ _ (by decide), hsi₂])

/-- `permuteAt`: calling `vg_keccak_f1600` on the state at `rbx`, with
scratch space at `r15`. -/
theorem permuteAt_ok {s : State} {st scr : Addr} (hbx : s.gpr .rbx = st) (h15 : s.gpr .r15 = scr)
    (d₁ : Region.Disjoint ⟨st, 200⟩ ⟨scr, 512⟩) (d₂ : (below (s.gpr .rsp) 8).Disjoint ⟨st, 200⟩)
    (d₃ : (below (s.gpr .rsp) 8).Disjoint ⟨scr, 512⟩)
    (hw : Covers [⟨st, 200⟩, ⟨scr, 512⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨st, 200⟩, ⟨scr, 512⟩, below (s.gpr .rsp) 8] s.mem s'.mem →
      stateAt s'.mem st = keccakF (stateAt s.mem st) → Q s') :
    WP isa Impl.Sha3.X86_64.Stream.permuteAt s Q := by
  unfold Impl.Sha3.X86_64.Stream.permuteAt
  refine WP.seq (VG.Proof.Sha3.X86_64.wp_mov fun s₁ u₁ => VG.Proof.Sha3.X86_64.wp_mov fun s₂ u₂ => VG.Proof.Sha3.X86_64.wp_nil ?_)
  have sp₂ : s₂.gpr .rsp = s.gpr .rsp := by rw [u₂.other _ (by decide), u₁.other _ (by decide)]
  have cs₂ : ∀ r ∈ calleeSaved, s₂.gpr r = s.gpr r := fun r hr => by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [u₂.other _ (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      u₁.other _ (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
  refine WP.seq (VG.Proof.Sha3.X86_64.call_ok (st := st) (scr := scr)
    (by rw [u₂.other _ (by decide), u₁.gpr, hbx]) (by rw [u₂.gpr, u₁.other _ (by decide), h15])
    d₁ (by rw [sp₂]; exact d₂) (by rw [sp₂]; exact d₃) (by rw [u₂.wr, u₁.wr]; exact hw)
    fun s₃ rd₃ wr₃ cs₃ f₃ e₃ di₃ si₃ => VG.Proof.Sha3.X86_64.wp_mov fun s₄ u₄ => VG.Proof.Sha3.X86_64.wp_mov fun s₅ u₅ => VG.Proof.Sha3.X86_64.wp_nil ?_)
  refine hQ s₅ (by rw [u₅.rd, u₄.rd, rd₃, u₂.rd, u₁.rd]) (by rw [u₅.wr, u₄.wr, wr₃, u₂.wr, u₁.wr])
    (fun r hr => ?_) (by rw [u₅.mem, u₄.mem, ← u₁.mem, ← u₂.mem, ← sp₂]; exact f₃)
    (by rw [u₅.mem, u₄.mem, e₃, u₂.mem, u₁.mem])
  by_cases h1 : r = .r15
  · subst h1; rw [u₅.gpr, u₄.other _ (by decide), si₃, h15]
  · by_cases h2 : r = .rbx
    · subst h2; rw [u₅.other _ (by decide), u₄.gpr, di₃, hbx]
    · rw [u₅.other _ h1, u₄.other _ h2, cs₃ r hr, cs₂ r hr]

end VG.Proof.Sha3.X86_64

end

end

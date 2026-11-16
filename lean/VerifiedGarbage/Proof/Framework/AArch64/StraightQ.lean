module

public import VerifiedGarbage.Proof.Framework.AArch64.StraightV
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Omega

/-!
# AArch64: straight-line AdvSIMD code that permutes and XORs bytes, on whole vectors

As `StraightV`, for code whose results are not doubleword by doubleword:
a block of `eor`, `mov`, `tbl` by a register holding a known constant,
`rev32` of halfwords and `ldr q` of the external words `[ext, #16j]`
(`j < exts`, only read) is evaluated once over an abstract domain on
128-bit words. A `tbl` by constant indices below 16 permutes the bytes of
its table register: byte `k` of the result is byte `cₖ` of the table, which
is byte `k` of the table rotated right by `8 ((cₖ - k) mod 16)` bits, so the
result is the XOR over `d < 16` of the table rotated right by `8 d` bits,
masked to the bytes with `(cₖ - k) mod 16 = d` (`tblSel_eq`): rotations and
masks by constants, which the lane domain (`Bitslice.lanes`) tracks.
Nothing but vector registers is written.
-/

@[expose] public section

namespace VG.AArch64.StraightQ

open VG.Bitslice
open VG.AArch64.StraightV (vAddr addr_slot read16_readW exec_vop_some)

/-- The external words: `[ext, #16j]` for `j < exts`, only read. -/
structure Cfg where
  ext : Reg
  exts : Nat
  deriving DecidableEq, Repr

/-- The abstract values of the vector registers, and the registers known
to hold a constant (the indices of a `tbl`). -/
structure Env (α : Type) where
  reg : VReg → Option α
  idx : VReg → Option (BitVec 128) := fun _ => none

variable {α : Type}

def Env.setReg (e : Env α) (d : VReg) (v : α) : Env α :=
  { reg := fun r => if r = d then some v else e.reg r,
    idx := fun r => if r = d then none else e.idx r }

/-- The external word that `[n, #off]` (a 16-byte access) addresses, if any. -/
def Cfg.loc (c : Cfg) (n : Reg) (off : Nat) : Option Nat :=
  if n = c.ext ∧ off % 16 = 0 ∧ off / 16 < c.exts ∧ off < 65536 then some (off / 16) else none

/-! ## `tbl` by constant indices -/

/-- `tbl` of the table `x` by the indices `c`. -/
def tblSel (x c : BitVec 128) : BitVec 128 :=
  ofVBytes fun i => if (vbyte c i).toNat < 16 then vbyte x (vbyte c i).toNat else 0

/-- Whether every index is below 16. -/
def validIdx (c : BitVec 128) : Bool := (List.range 16).all fun k => (vbyte c k).toNat < 16

/-- The bytes `k` that the indices `c` take from `d` bytes above (modulo 16). -/
def permMask (c : BitVec 128) (d : Nat) : BitVec 128 :=
  ofVBytes fun k => if ((vbyte c k).toNat + 16 - k) % 16 = d then 0xFF else 0

/-- `rev32` of halfwords, as indices. -/
def revIdx : BitVec 128 := ofVBytes fun i => BitVec.ofNat 8 (4 * (i / 4) + (i % 4 + 2) % 4)

theorem vbyte_and (x y : BitVec 128) (e : Nat) : vbyte (x &&& y) e = vbyte x e &&& vbyte y e := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [vbyte, hi]

theorem vbyte_xor (x y : BitVec 128) (e : Nat) : vbyte (x ^^^ y) e = vbyte x e ^^^ vbyte y e := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [vbyte, hi]

theorem vbyte_ext {x y : BitVec 128} (h : ∀ e < 16, vbyte x e = vbyte y e) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have := congrArg (·.getLsbD (i % 8)) (h (i / 8) (by omega_using [hi]))
  simp only [vbyte, BitVec.getLsbD_extractLsb', Nat.mod_lt _ (show 0 < 8 by decide), decide_true,
    Bool.true_and] at this
  rwa [show 8 * (i / 8) + i % 8 = i by omega_using []] at this

/-- Byte `k` of `x` rotated right by `d` bytes. -/
theorem vbyte_rotateRight (x : BitVec 128) {d k : Nat} (hd : d < 16) (hk : k < 16) :
    vbyte (x.rotateRight (8 * d)) k = vbyte x ((k + d) % 16) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vbyte, BitVec.getLsbD_extractLsb', decide_eq_true hi, Bool.true_and]
  rw [BitVec.getLsbD_rotateRight_of_lt (by omega_using [hd])]
  have hlt : 8 * k + i < 128 := by omega_using [hk, hi]
  by_cases h : 8 * k + i < 128 - 8 * d
  · rw [ite_eq_left h, Nat.mod_eq_of_lt (by omega_using [h])]
    congr 1; omega_using []
  · rw [ite_eq_right h, show (k + d) % 16 = k + d - 16 by omega_using [h, hk, hd, hi],
      decide_eq_true hlt, Bool.true_and]
    congr 1; omega_using [h, hk, hd, hi]

/-- The XOR over a range of values of which all but one are zero. -/
theorem foldl_xor_single (f : Nat → BitVec 8) {n d₀ : Nat} (hd : d₀ < n)
    (hz : ∀ d < n, d ≠ d₀ → f d = 0) :
    (List.range n).foldl (fun acc d => acc ^^^ f d) 0 = f d₀ := by
  induction n with
  | zero => omega_using [hd]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases h : d₀ = n
    · subst h
      have : (List.range d₀).foldl (fun acc d => acc ^^^ f d) 0 = 0 := by
        clear ih hd
        have hz' : ∀ d < d₀, f d = 0 := fun d hd' => hz d (by omega_using [hd']) (by omega_using [hd'])
        clear hz
        induction d₀ with
        | zero => rfl
        | succ m ih =>
          rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
            ih fun d hd' => hz' d (by omega_using [hd']), hz' m (by omega_using [])]
          simp
      rw [this]; simp
    · rw [ih (by omega_using [hd, h]) fun d hd' hne => hz d (by omega_using [hd']) hne,
        hz n (by omega_using []) (Ne.symm h)]
      simp

theorem vbyte_foldl_xor (g : Nat → BitVec 128) (l : List Nat) (z : BitVec 128) (k : Nat) :
    vbyte (l.foldl (fun acc d => acc ^^^ g d) z) k =
      l.foldl (fun acc d => acc ^^^ vbyte (g d) k) (vbyte z k) := by
  induction l generalizing z with
  | nil => rfl
  | cons d l ih => rw [List.foldl_cons, List.foldl_cons, ih, vbyte_xor]

theorem validIdx_lt {c : BitVec 128} (h : validIdx c = true) {k : Nat} (hk : k < 16) :
    (vbyte c k).toNat < 16 := by
  have := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  simpa using this

/-- A `tbl` by valid indices, as rotations and masks. -/
theorem tblSel_eq (x c : BitVec 128) (hc : validIdx c = true) :
    tblSel x c =
      (List.range 16).foldl (fun acc d => acc ^^^ (x.rotateRight (8 * d) &&& permMask c d)) 0 := by
  refine vbyte_ext fun k hk => ?_
  have hck := validIdx_lt hc hk
  rw [tblSel, vbyte_ofVBytes _ hk, ite_eq_left hck, vbyte_foldl_xor]
  have h0 : vbyte (0 : BitVec 128) k = 0 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [vbyte]
  rw [h0, foldl_xor_single _ (d₀ := ((vbyte c k).toNat + 16 - k) % 16) (Nat.mod_lt _ (by decide))]
  · rw [vbyte_and, vbyte_rotateRight _ (Nat.mod_lt _ (by decide)) hk, permMask, vbyte_ofVBytes _ hk,
      ite_eq_left rfl, show (k + ((vbyte c k).toNat + 16 - k) % 16) % 16 = (vbyte c k).toNat by
        omega_using [hk, hck], show (0xFF : BitVec 8) = BitVec.allOnes 8 from rfl, BitVec.and_allOnes]
  · intro d _ hne
    rw [vbyte_and, permMask, vbyte_ofVBytes _ hk, ite_eq_right (Ne.symm hne)]
    simp

theorem validIdx_revIdx : validIdx revIdx = true := by decide +kernel

theorem rev32h_eq (x : BitVec 128) : VRevOp.rev32h.eval x = tblSel x revIdx := by
  refine vbyte_ext fun k hk => ?_
  have hv : (vbyte revIdx k).toNat = 4 * (k / 4) + (k % 4 + 2) % 4 := by
    rw [revIdx, vbyte_ofVBytes _ hk, BitVec.toNat_ofNat]; omega_using [hk]
  rw [tblSel, vbyte_ofVBytes _ hk, hv, ite_eq_left (by omega_using [hk]), VRevOp.eval, vbyte_ofVBytes _ hk]

/-! ## The evaluator -/

section
variable (D : Dom α 128) (c : Cfg)

/-- One term of `tblSel_eq`: `acc ⊕ (a ⋙ 8 d) ∧ permMask c d`, skipped when the mask is zero. -/
def permStep (cs : BitVec 128) (a acc : α) (d : Nat) : Option α :=
  if permMask cs d = 0 then some acc else
    (D.ror (8 * d) a).bind fun r => (D.const (permMask cs d)).bind fun m =>
      (D.and r m).bind fun t => D.xor acc t

def permFrom (cs : BitVec 128) (a : α) : List Nat → α → Option α
  | [], acc => some acc
  | d :: ds, acc => (permStep D cs a acc d).bind (permFrom cs a ds)

/-- The bytes of `a` permuted by the indices `cs`. -/
def perm (cs : BitVec 128) (a : α) : Option α :=
  (D.const 0).bind (permFrom D cs a (List.range 16))

/-- The instruction's effect on the abstract values; `x j` is external word `j`. -/
def step (x : Nat → Option α) (e : Env α) : Instr → Option (Env α)
  | .vop (.logic .eor d n m) =>
    match e.reg n, e.reg m with
    | some a, some b => (D.xor a b).map (e.setReg d)
    | _, _ => none
  | .vop (.mov d n) => (e.reg n).map (e.setReg d)
  | .vop (.tbl d n m) =>
    match e.reg n, e.idx m with
    | some a, some cs => if validIdx cs then (perm D cs a).map (e.setReg d) else none
    | _, _ => none
  | .vop (.rev .rev32h d n) => (e.reg n).bind fun a => (perm D revIdx a).map (e.setReg d)
  | .ldrq t n off => match c.loc n off with
    | some k => (x k).map (e.setReg t)
    | none => none
  | _ => none

def eval (x : Nat → Option α) : List Instr → Env α → Option (Env α)
  | [], e => some e
  | i :: is, e => (step D c x e i).bind (eval x is)

def check (x : Nat → Option α) (is : List Instr) (e : Env α) (post : Env α → Bool) : Bool :=
  match eval D c x is e with
  | some e' => post e'
  | none => false

theorem of_check {x : Nat → Option α} {is : List Instr} {e : Env α} {post : Env α → Bool}
    (h : check D c x is e post = true) : ∃ e', eval D c x is e = some e' ∧ post e' = true := by
  unfold check at h
  split at h
  · exact ⟨_, by assumption, h⟩
  · cases h

end

/-! ## Relating abstract and machine states -/

structure Rel (R : α → BitVec 128 → Prop) (c : Cfg) (x : Nat → Option α) (e : Env α) (s : State) :
    Prop where
  reg : ∀ r a, e.reg r = some a → R a (s.v r)
  idx : ∀ r v, e.idx r = some v → s.v r = v
  ext : ∀ k a, k < c.exts → x k = some a → R a (s.mem.readW (vAddr (s.gpr c.ext) k) 128)

/-- The external words are readable. -/
def Ok (c : Cfg) (s : State) : Prop :=
  ∀ k < c.exts, InRegions (s.rd ++ s.wr) (vAddr (s.gpr c.ext) k) 16

section
variable {D : Dom α 128} {R : α → BitVec 128 → Prop} {c : Cfg} {x : Nat → Option α}

theorem permFrom_sound (hD : D.Sound R) {cs : BitVec 128} {a : α} {v : BitVec 128} (ha : R a v) :
    ∀ (l : List Nat) {acc r : α} {z : BitVec 128}, R acc z → permFrom D cs a l acc = some r →
      R r (l.foldl (fun acc d => acc ^^^ (v.rotateRight (8 * d) &&& permMask cs d)) z) := by
  intro l
  induction l with
  | nil => intro acc r z hz h; cases h; exact hz
  | cons d l ih =>
    intro acc r z hz h
    simp only [permFrom, Option.bind_eq_some_iff] at h
    obtain ⟨acc', h₁, h₂⟩ := h
    rw [List.foldl_cons]
    refine ih ?_ h₂
    simp only [permStep] at h₁
    split at h₁
    · rename_i h0
      cases h₁
      rw [h0]; simpa using hz
    · simp only [Option.bind_eq_some_iff] at h₁
      obtain ⟨r₁, hr, m, hm, t, ht, hx⟩ := h₁
      exact hD.xor hz (hD.and (hD.ror ha hr) (hD.const hm) ht) hx

theorem perm_sound (hD : D.Sound R) {cs : BitVec 128} (hcs : validIdx cs = true) {a r : α}
    {v : BitVec 128} (ha : R a v) (h : perm D cs a = some r) : R r (tblSel v cs) := by
  simp only [perm, Option.bind_eq_some_iff] at h
  obtain ⟨z, hz, h⟩ := h
  rw [tblSel_eq _ _ hcs]
  exact permFrom_sound hD ha _ (hD.const hz) h

/-- What a block leaves: the abstract values related, and nothing but the
vector registers it writes changed. -/
structure Post (R : α → BitVec 128 → Prop) (c : Cfg) (x : Nat → Option α) (e' : Env α)
    (s s' : State) (writes : VReg → Prop) : Prop where
  rel : Rel R c x e' s'
  same : s' = { s with v := s'.v }
  other : ∀ r, ¬ writes r → s'.v r = s.v r

theorem post_setV {e : Env α} {s : State} (hrel : Rel R c x e s) {d : VReg} {a : α}
    {v : BitVec 128} (hv : R a v) : Post R c x (e.setReg d a) s (s.setV d v) (· = d) where
  rel := {
    reg := fun r b h => by
      simp only [Env.setReg] at h
      simp only [State.setV]
      split at h
      · rename_i hr; cases h; simp only [hr, ite_true]; exact hv
      · rename_i hr; simp only [hr, ite_false]; exact hrel.reg r b h
    idx := fun r w h => by
      simp only [Env.setReg] at h
      simp only [State.setV]
      split at h
      · cases h
      · rename_i hr; simp only [hr, ite_false]; exact hrel.idx r w h
    ext := fun k b hk h => by simpa [State.setV] using hrel.ext k b hk h }
  same := rfl
  other r hr := by simp [State.setV, hr]

theorem loc_some {n : Reg} {off k : Nat} (h : c.loc n off = some k) :
    n = c.ext ∧ off = 16 * k ∧ k < c.exts ∧ off < 65536 := by
  unfold Cfg.loc at h
  split at h
  · rename_i h1
    cases h
    obtain ⟨hb, hm, hlt, h64⟩ := h1
    exact ⟨hb, by omega_using [hm], hlt, h64⟩
  · cases h

theorem step_ok (hD : D.Sound R) {e e' : Env α} {s : State} (hok : Ok c s) (hrel : Rel R c x e s)
    {i : Instr} (h : step D c x e i = some e') :
    ∃ s', exec i s = some s' ∧ Post R c x e' s s' (fun r => vdstOf i = some r) := by
  cases i with
  | vop op =>
    cases op with
    | logic op d n m =>
      cases op <;> simp only [step] at h <;> try cases h
      split at h
      · rename_i a b ha hb
        obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
        refine ⟨_, exec_vop_some rfl, ?_⟩
        have := post_setV (d := d) hrel (hD.xor (hrel.reg n a ha) (hrel.reg m b hb) ht)
        exact { this with other := fun r hr => this.other r fun hw => hr (by simp [vdstOf, VOp.dst, hw]) }
      · cases h
    | mov d n =>
      simp only [step] at h
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      refine ⟨_, exec_vop_some rfl, ?_⟩
      have := post_setV (d := d) hrel (hrel.reg n a ha)
      exact { this with other := fun r hr => this.other r fun hw => hr (by simp [vdstOf, VOp.dst, hw]) }
    | tbl d n m =>
      simp only [step] at h
      split at h
      · rename_i a cs ha hcs
        split at h
        · rename_i hv
          obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
          refine ⟨_, exec_vop_some rfl, ?_⟩
          have := post_setV (d := d) hrel (perm_sound hD hv (hrel.reg n a ha) ht)
          rw [hrel.idx m cs hcs]
          exact { this with other := fun r hr => this.other r fun hw => hr (by simp [vdstOf, VOp.dst, hw]) }
        · cases h
      · cases h
    | rev op d n =>
      cases op <;> simp only [step] at h <;> try cases h
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨a, ha, h⟩ := h
      obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
      refine ⟨_, exec_vop_some rfl, ?_⟩
      have := post_setV (d := d) hrel (perm_sound hD validIdx_revIdx (hrel.reg n a ha) ht)
      rw [rev32h_eq]
      exact { this with other := fun r hr => this.other r fun hw => hr (by simp [vdstOf, VOp.dst, hw]) }
    | _ => simp [step] at h
  | ldrq t n off =>
    simp only [step] at h
    split at h
    · rename_i k hk
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hb, hoff, hlt, h64⟩ := loc_some hk
      subst hb hoff
      refine ⟨s.setV t (s.mem.readW (vAddr (s.gpr c.ext) k) 128), ?_, ?_⟩
      · simp [exec, addr_slot h64, State.load, hok k hlt, read16_readW]
      · have := post_setV (d := t) hrel (hrel.ext k a hlt ha)
        exact { this with other := fun r hr => this.other r fun hw => hr (by simp [vdstOf, hw]) }
    · cases h
  | _ => simp [step] at h

theorem Ok.congr {s s' : State} (h : Ok c s) (hs : s' = { s with v := s'.v }) : Ok c s' := by
  intro k hk
  rw [hs]; exact h k hk

theorem run (hD : D.Sound R) {is : List Instr} {e e' : Env α} {s : State}
    (hok : Ok c s) (hrel : Rel R c x e s) (h : eval D c x is e = some e') :
    ∃ s', runBlock isa is s = some s' ∧
      Post R c x e' s s' (fun r => (is.all fun i => vdstOf i != some r) = false) := by
  induction is generalizing e s with
  | nil =>
    cases h
    exact ⟨s, runBlock_nil, hrel, rfl, fun _ _ => rfl⟩
  | cons i is ih =>
    simp only [eval, Option.bind_eq_some_iff] at h
    obtain ⟨e₁, h₁, h₂⟩ := h
    obtain ⟨s₁, hs₁, p₁⟩ := step_ok hD hok hrel h₁
    obtain ⟨s', hs', p⟩ := ih (hok.congr p₁.same) p₁.rel h₂
    refine ⟨s', by rw [runBlock_cons, hs₁, runStep_some]; exact hs', p.rel, ?_, fun r hr => ?_⟩
    · rw [p.same, p₁.same]
    · simp only [List.all_cons, Bool.and_eq_false_iff, bne_eq_false_iff_eq, not_or] at hr
      exact (p.other r hr.2).trans (p₁.other r hr.1)

end

/-! ## Linear layers, on input words given as atoms -/

/-- The registers `ins` hold input words, and the registers `cs` constants. -/
def linEnv (ins : List (VReg × Nat)) (cs : List (VReg × BitVec 128)) : Env (Nat × Nat) :=
  { reg := fun r => (ins.find? (·.1 == r)).map (inWordW 128 ·.2),
    idx := fun r => (cs.find? (·.1 == r)).map (·.2) }

/-- External word `j` is input word `xb + j`. -/
def linExt (xb j : Nat) : Option (Nat × Nat) := some (inWordW 128 (xb + j))

/-- Each output register `r` holds `outWordW 128 g`, below `2 ^ (128 2 ^ k)` (`outOkW`). -/
def linPost (k : Nat) (outs : List (VReg × (Nat → List Nat))) (e : Env (Nat × Nat)) : Bool :=
  outs.all fun o => outOkW 128 k (e.reg o.1) o.2

/-- A linear block that the evaluator accepts, on the machine: bit `p` of
each output register is the XOR of the input bits `g p`, and nothing but
vector registers the block writes is changed. -/
theorem linear_ok {k xb : Nat} {c : Cfg} {is : List Instr} {ins : List (VReg × Nat)}
    {cs : List (VReg × BitVec 128)} {outs : List (VReg × (Nat → List Nat))}
    (hchk : check (lanes 128 k) c (linExt xb) is (linEnv ins cs) (linPost k outs) = true)
    {s : State} (hok : Ok c s) (W : Nat → BitVec 128)
    (hin : ∀ r i, (r, i) ∈ ins → 128 * i + 128 ≤ 2 ^ k ∧ W i = s.v r)
    (hcs : ∀ r v, (r, v) ∈ cs → s.v r = v)
    (hext : ∀ j < c.exts,
      128 * (xb + j) + 128 ≤ 2 ^ k ∧ W (xb + j) = s.mem.readW (vAddr (s.gpr c.ext) j) 128) :
    ∃ s', runBlock isa is s = some s' ∧
      (∀ r g, (r, g) ∈ outs → ∀ p < 128, (s'.v r).getLsbD p = xorBits W (g p)) ∧
      s' = { s with v := s'.v } ∧
      (∀ r, (is.all fun i => vdstOf i != some r) = true → s'.v r = s.v r) := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ hchk
  have hrel : Rel (LaneRel k (assign W (2 ^ k))) c (linExt xb) (linEnv ins cs) s := by
    refine ⟨fun r a h => ?_, fun r v h => ?_, fun j a hj h => ?_⟩
    · simp only [linEnv, Option.map_eq_some_iff] at h
      obtain ⟨⟨r', i⟩, hf, rfl⟩ := h
      have hr : r' = r := by simpa using List.find?_some hf
      subst hr
      obtain ⟨h1, h2⟩ := hin r' i (List.mem_of_find?_eq_some hf)
      rw [← h2]; exact inWordW_rel W h1
    · simp only [linEnv, Option.map_eq_some_iff] at h
      obtain ⟨cv, hf, rfl⟩ := h
      have hr : cv.1 = r := by simpa using List.find?_some hf
      rw [← hr]; exact hcs cv.1 cv.2 (List.mem_of_find?_eq_some hf)
    · simp only [linExt, Option.some.injEq] at h; subst h
      obtain ⟨h1, h2⟩ := hext j hj
      rw [← h2]; exact inWordW_rel W h1
  obtain ⟨s', hs', p⟩ := run lanes_sound hok hrel he
  refine ⟨s', hs', fun r g hrg q hq => ?_, p.same, fun r hr => p.other r (by simp [hr])⟩
  obtain ⟨h1, h2⟩ := outOkW_spec (List.all_eq_true.mp hpost (r, g) hrg)
  exact outWordW_rel_of_lt h2 (p.rel.reg r _ h1) q hq

end VG.AArch64.StraightQ

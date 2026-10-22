module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Search
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Finish
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Entry
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Intro
import VerifiedGarbage.Proof.Dsa.Arm.Gen.SpCT
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on ARMv7: the body

`body_vp`: from the frame just allocated, the entry, the search and the exit
of the geometry `p_len` selects (`dispatch_vp`, each geometry given by a
`GeoOk`), and the callee-saved registers restored (`restore_vp`): `Done`.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_cmp op2_imm eval_eq)
open VG.Proof.Rsa.Arm.Recover (VP)

/-- A geometry's proofs, for every call with its `p_len` (and so its `q_len`). -/
structure GeoOk (g : Geo) (pL qL : Nat) where
  HO : HashOk g.G
  n : Nat
  ok : ∀ G : GP, (∃ σ, CIn σ ∧ mkG σ = G) → G.pLen = pL → G.qLen = qL → GenOk G g HO n
  hlb : HO.md.lenBytes qL =
    [0, 0, 0, 0, 0, 0, BitVec.ofNat 8 (8 * qL / 256), BitVec.ofNat 8 (8 * qL % 256)]

/-- What the search returns. -/
abbrev sRes (G : GP) : Option Spec.Dsa.Params :=
  Spec.Dsa.generateParameters.attempt (8 * G.pLen) (hsL G) (8 * G.qLen)
    (Spec.Dsa.generationChunks G.qLen G.seedsB) G.witB

section
variable {G : GP}

theorem beq_toNat (x y : BitVec 32) : (x == y) = decide (x.toNat = y.toNat) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, BitVec.toNat_inj]

/-- After the entry. -/
abbrev E1 (G : GP) (σ s : State) : Prop := GI G σ (eV G) eLS s ∧ s.gpr .r2 = σ.gpr .r2

/-- `cmp r2, #x`: whether `p_len` is `x`. -/
theorem cmp_vp {x : BitVec 32} (hx : ∀ s, (Op2.imm x).eval s = some x) :
    VP (E1 G) (.block [.cmp .r2 (.imm x)])
      (fun σ s => E1 G σ s ∧ isa.eval .eq s = some (decide (G.pLen = x.toNat))) := by
  refine VP.taint [.r2] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r2])
      (.block [.cmp .r2 (.imm x)]), rfl⟩ (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s h => ?_
  · simp only [List.mem_singleton] at hr; subst hr
    apply BitVec.eq_of_toNat_eq
    rw [h₁.2, h₂.2]
    have e₁ : (σ₁.gpr .r2).toNat = G.pLen := by rw [← h₁.1.hG]; rfl
    have e₂ : (σ₂.gpr .r2).toNat = G.pLen := by rw [← h₂.1.hG]; rfl
    rw [e₁, e₂]
  refine wp_cmp (hx s) fun s' f z => WP.block_nil ⟨⟨h.1.of_rest (f.rest []) f.mem, by rw [f.gpr]; exact h.2⟩, ?_⟩
  rw [eval_eq, z, beq_sub_zero, beq_toNat, h.2]
  have e : (σ.gpr .r2).toNat = G.pLen := by rw [← h.1.hG]; rfl
  rw [e]

/-- A geometry's search and exit. -/
theorem gen_vp {g : Geo} {pL qL : Nat} (K : GeoOk g pL qL) (hex : ∃ σ, CIn σ ∧ mkG σ = G)
    (hp : G.pLen = pL) (hq : G.qLen = qL) {F : State → State → Prop} (hF : ∀ σ s, F σ s → E1 G σ s) :
    VP F g.generate (fun σ t => FO G (sRes G) σ t ∧ True) := by
  have O := K.ok G hex hp hq
  refine VP.seq ((search_vp (X := fun _ => True) O (by rw [hq]; exact K.hlb) (by decide) (eV_fSeed G)
    (by decide) (eV_fSeedLeft G) (by decide) (eV_fStatus G) (by decide) (eV_fUsed G)).mono
      (fun σ s h => ⟨(hF σ s h).1, trivial⟩) fun _ _ h => h) (finish_vp O.hp O.hq _)

/-- The geometry `p_len` selects. -/
theorem dispatch_vp {g1 g2 g3 : Geo} (K1 : GeoOk g1 128 20) (K2 : GeoOk g2 256 32) (K3 : GeoOk g3 384 32) :
    VP (E1 G) (dispatch g1 g2 g3) (fun σ t => FO G (sRes G) σ t ∧ True) := by
  refine (VP.intro (P := ∃ σ, CIn σ ∧ mkG σ = G) fun hex => ?_).mono
    (fun σ s h => ⟨⟨σ, h.1.pre, h.1.hG⟩, h⟩) fun _ _ h => h
  obtain ⟨σ₀, pre₀, hG₀⟩ := hex
  have hl := pre₀.lens'
  rw [hG₀] at hl
  unfold dispatch
  refine VP.seq (cmp_vp (G := G) (x := 128) fun s => op2_imm (by decide)) ?_
  have hc : ∀ {F : State → State → Prop} {b : Prop} [Decidable b],
      (∀ σ s, F σ s → isa.eval .eq s = some (decide b)) →
      ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → isa.eval .eq s₁ = isa.eval .eq s₂ :=
    fun hF _ _ _ _ h₁ h₂ => by rw [hF _ _ h₁, hF _ _ h₂]
  have no : ∀ {F : State → State → Prop} {c : Prog isa} {Q : State → State → Prop} {b : Bool} {p : Prop}
      [Decidable p], ¬ (decide p = b) →
      VP (fun σ s => (F σ s ∧ isa.eval .eq s = some (decide p)) ∧ isa.eval .eq s = some b) c Q :=
    fun hb => VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => hb (by rw [e] at z; exact Option.some.inj z)
  rcases hl with ⟨h1, h1'⟩ | ⟨h2, h2'⟩ | ⟨h3, h3'⟩
  · refine VP.ite (hc fun σ s h => h.2) (gen_vp K1 ⟨σ₀, pre₀, hG₀⟩ h1 h1' fun σ s h => h.1.1)
      (no (by simp [h1]))
  · refine VP.ite (hc fun σ s h => h.2) (no (by simp [h2]))
      (VP.seq ((cmp_vp (G := G) (x := 0x100) fun s => op2_imm (by decide)).mono (fun σ s h => h.1.1) fun _ _ h => h)
        (VP.ite (hc fun σ s h => h.2) (gen_vp K2 ⟨σ₀, pre₀, hG₀⟩ h2 h2' fun σ s h => h.1.1) (no (by simp [h2]))))
  · refine VP.ite (hc fun σ s h => h.2) (no (by simp [h3]))
      (VP.seq ((cmp_vp (G := G) (x := 0x100) fun s => op2_imm (by decide)).mono (fun σ s h => h.1.1) fun _ _ h => h)
        (VP.ite (hc fun σ s h => h.2) (no (by simp [h3])) (gen_vp K3 ⟨σ₀, pre₀, hG₀⟩ h3 h3' fun σ s h => h.1.1)))

end

/-! ## Restoring the registers -/

theorem loads_ok {g : Reg → BitVec 32} {B : BitVec 32} : ∀ (l : List (Reg × Nat)) (s : State)
    {rest : List Instr} {Q : State → Prop}, (l.map Prod.fst).Nodup → s.sp = B →
    (∀ p ∈ l, p.2 < 4096 ∧ InRegions (s.rd ++ s.wr) (State.addr (B + BitVec.ofNat 32 p.2)) 4 ∧
      s.mem.readW (State.addr (B + BitVec.ofNat 32 p.2)) 32 = g p.1) →
    (∀ t, Rest (l.map Prod.fst) s t → t.mem = s.mem → (∀ p ∈ l, t.gpr p.1 = g p.1) → WP isa (.block rest) t Q) →
    WP isa (.block (l.map (fun p => Instr.ldrSp p.1 p.2) ++ rest)) s Q
  | [], s, _, _, _, _, _, k => k s (Rest.refl _ _) rfl fun _ h => nomatch h
  | p :: l, s, rest, Q, hn, hsp, hl, k => by
    obtain ⟨h1, h2, h3⟩ := hl p List.mem_cons_self
    have hn' := List.nodup_cons.mp hn
    simp only [List.map_cons, List.cons_append]
    refine VG.Proof.Bignum.Arm.wp_loadStack h1 (by rw [hsp]) h2 fun s₁ u => ?_
    rw [h3] at u
    refine loads_ok (g := g) l s₁ hn'.2 (u.sp.trans hsp) (fun q hq => ?_) fun t R m hq => k t ?_ (m.trans u.mem) ?_
    · obtain ⟨a, b, c⟩ := hl q (List.mem_cons_of_mem _ hq)
      exact ⟨a, by rw [u.rd, u.wr]; exact b, by rw [u.mem]; exact c⟩
    · exact (u.rest List.mem_cons_self).trans (R.mono fun r hr => List.mem_cons_of_mem _ hr)
    · intro q hq'
      rcases List.mem_cons.mp hq' with rfl | hq'
      · rw [R.gpr _ hn'.1, u.gpr]
      · exact hq q hq'

/-- Done, the frame still allocated: the registers restored. -/
structure Done (G : GP) (R : Option Spec.Dsa.Params) (σ t : State) : Prop where
  pre : CIn σ
  hG : mkG σ = G
  sp : t.sp = G.sp
  rd : t.rd = σ.rd
  wr : t.wr = G.rFrame :: σ.wr
  regs : ∀ p ∈ VG.Impl.Dsa.Arm.Generation.saved, t.gpr p.1 = σ.gpr p.1
  out : Spec.Rsa.bytesAt t.mem (State.addr G.out) G.outLen =
    (R.map (Spec.Dsa.encodeParams G.pLen G.qLen)).getD (List.replicate G.outLen 0)
  r0 : t.gpr .r0 = BitVec.ofNat 32 (if R.isSome then 1 else 0)

theorem restore_vp {G : GP} {R : Option Spec.Dsa.Params} :
    VP (fun σ t => FO G R σ t ∧ True) (.block restore) (Done G R) := by
  show VP _ (.block (VG.Impl.Dsa.Arm.Generation.saved.map fun p => Instr.ldrSp p.1 p.2)) _
  refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.1.sp, h₂.1.sp]) fun σ s ⟨h, _⟩ => ?_
  have spN := h.pre.spN; have spLo := h.pre.spLo; rw [h.hG] at spN
  rw [← List.append_nil (List.map _ _)]
  refine loads_ok (g := σ.gpr) (B := G.sp) _ s (by decide) h.sp (fun p hp => ?_) fun t R m hr => WP.block_nil
    ⟨h.pre, h.hG, R.sp.trans h.sp, R.rd.trans h.rd, R.wr.trans h.wr, hr, by rw [m]; exact h.out,
      by rw [R.gpr _ (by decide)]; exact h.r0⟩
  have hb := saved_ok p hp
  have ea : State.addr (G.sp + BitVec.ofNat 32 p.2) = State.addr G.sp + BitVec.ofNat 64 p.2 :=
    addr_add (by simp only [F] at *; omega)
  refine ⟨by omega, ?_, by rw [ea]; exact h.saved p hp⟩
  rw [ea]
  exact ⟨G.rFrame, List.mem_append_right _ (by rw [h.wr]; exact List.mem_cons_self),
    Offset.contains_base _ (by simp only [F]; omega) (by simp only [F] at *; omega)⟩

/-! ## The body -/

/-- The frame just allocated, for a call with the public parameters `G`. -/
abbrev AE (G : GP) (σ u : State) : Prop := u = allocated F σ ∧ CIn σ ∧ mkG σ = G

theorem entry_vp {G : GP} : VP (AE G) (.block entry) (E1 G) := by
  refine VP.of_ct (fun σ₁ σ₂ => ?_) fun σ u ⟨hu, hpre, hG⟩ => by subst hu hG; exact entry_ok hpre
  unfold entry
  refine (RelCT.block_append (M := isa) (l₁ := [.addSp .r12 0])
    ((addSp_ct 0).seq (spBlock_ct _ (by decide)))).mono (fun s₁ s₂ ⟨⟨h₁, _, g₁⟩, ⟨h₂, _, g₂⟩⟩ => ?_)
      fun _ _ _ => trivial
  subst h₁ h₂
  show σ₁.sp - BitVec.ofNat 32 F = σ₂.sp - BitVec.ofNat 32 F
  have e₁ : σ₁.sp = G.sp0 := by rw [← g₁]; rfl
  have e₂ : σ₂.sp = G.sp0 := by rw [← g₂]; rfl
  rw [e₁, e₂]

theorem body_vp {G : GP} {g1 g2 g3 : Geo} (K1 : GeoOk g1 128 20) (K2 : GeoOk g2 256 32) (K3 : GeoOk g3 384 32) :
    VP (AE G) (.seq (.block entry) (.seq (dispatch g1 g2 g3) (.block restore))) (Done G (sRes G)) :=
  entry_vp.seq ((dispatch_vp K1 K2 K3).seq restore_vp)

end VG.Proof.Dsa.Arm.Gen

module

public import VerifiedGarbage.Impl.MlDsa.PPC64LE.PkTr
public import VerifiedGarbage.Spec.MlDsa.PkTr
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.StepsCT
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Piece
public import VerifiedGarbage.Proof.MlKem.PPC64LE.TopSave
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Contracts
import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Seeds
import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Impl.MlDsa.PPC64LE.PkTr
meta import VerifiedGarbage.Spec.MlDsa.PkTr
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.StepsCT
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Piece
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.TopSave
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Contracts
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Seeds
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig

/-!
# ML-DSA on PPC64LE: `vg_mldsa*_pk_tr`

Untrusted: everything here is checked by Lean. The function
(`Impl/MlDsa/PPC64LE/PkTr.lean`) in the setting of ML-DSA's top-level
functions (`Proof/MlDsa/PPC64LE/KeyGen/Site.lean`): five buffers (`lay`):
`scratch`, the 48 bytes of stack, `pk` (twice, at `r30` and `r29`, read
only) and `tr`; the prologue (`pro_ok`), the sponge (`hashS`, `hashS_tr`, of
the buffers but the first copy of `pk`) and the epilogue (`topEnd_ok`), as
pieces (`Piece`). Nothing is leaked but the pointers.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.PkTr

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Impl.MlDsa.PPC64LE.PkTr
open VG.Impl.MlKem.PPC64LE (topEnd)
open VG.Impl.Sha3.PPC64LE.Stream (mov)
open VG.Proof.MlDsa.PPC64LE.KeyGen (Site OkW disjW disjW' ix hashLay hashS hashS_tr pieceS Piece Rel2 relStart
  rel_of Two taint31 hashLay_ptr ix_ne1 shake31 reg)
open VG.Spec.MlDsa (Params scratchWords mlDsa44 mlDsa65 mlDsa87)
open VG.Spec.Sha3 (bytesAt)

/-- The size of `scratch`, in bytes. -/
abbrev scrLen (p : Params) : Nat := scratchWords p * 8

/-- The parameter sets. -/
abbrev PS (p : Params) : Prop := p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87

/-! ## The precondition -/

/-- The precondition of `pkTrContract` with 48 bytes of stack. -/
structure Pre (p : Params) (σ : State) : Prop where
  stk : 48 ≤ σ.sp.toNat
  rd : σ.rd = [reg (σ.gpr .r3) p.pkLen]
  wr : σ.wr = [reg (σ.gpr .r4) 64, reg (σ.gpr .r5) (scrLen p)]
  d_pt : (reg (σ.gpr .r3) p.pkLen).Disjoint (reg (σ.gpr .r4) 64)
  d_pc : (reg (σ.gpr .r3) p.pkLen).Disjoint (reg (σ.gpr .r5) (scrLen p))
  d_tc : (reg (σ.gpr .r4) 64).Disjoint (reg (σ.gpr .r5) (scrLen p))
  b_p : (below σ.sp 48).Disjoint (reg (σ.gpr .r3) p.pkLen)
  b_t : (below σ.sp 48).Disjoint (reg (σ.gpr .r4) 64)
  b_c : (below σ.sp 48).Disjoint (reg (σ.gpr .r5) (scrLen p))
  f_p : (σ.gpr .r3).toNat + p.pkLen ≤ 2 ^ 64
  f_t : (σ.gpr .r4).toNat + 64 ≤ 2 ^ 64
  f_c : (σ.gpr .r5).toNat + scrLen p ≤ 2 ^ 64

theorem pre_of {p : Params} {σ : State} (h : (Spec.MlDsa.pkTrContract p PPC64LE.abi 48).pre σ) : Pre p σ := by
  sig_pre [Spec.MlDsa.pkTrContract, Spec.MlDsa.pkTrSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

/-- The public data of `pkTrContract`. -/
def ptPub (σ₁ σ₂ : State) : Prop :=
  σ₁.sp = σ₂.sp ∧ σ₁.gpr .r3 = σ₂.gpr .r3 ∧ σ₁.gpr .r4 = σ₂.gpr .r4 ∧ σ₁.gpr .r5 = σ₂.gpr .r5

/-! ## The buffers -/

/-- `scratch` (0), the stack (1), `pk` (2 and 3) and `tr` (4). -/
def lay (p : Params) (σ : State) : Lay :=
  ⟨fun i => [σ.gpr .r5, σ.sp - BitVec.ofNat 64 48, σ.gpr .r3, σ.gpr .r3, σ.gpr .r4].getD i 0,
    [scrLen p, 48, p.pkLen, p.pkLen, 64]⟩

/-- The buffers written: `scratch`, the stack and `tr`. -/
abbrev tWb : List Nat := [0, 1, 4]

theorem lay_pub {p : Params} {σ₁ σ₂ : State} (h : ptPub σ₁ σ₂) : lay p σ₁ = lay p σ₂ := by
  obtain ⟨e0, e1, e2, e3⟩ := h
  simp only [lay]
  rw [e0, e1, e2, e3]

theorem lay_ok {p : Params} {σ : State} (hp : Pre p σ) : OkW (lay p σ) tWb := by
  have es : (⟨σ.sp - BitVec.ofNat 64 48, 48⟩ : Region) = below σ.sp 48 := rfl
  refine ⟨fun i hi => ?_, fun i hi j hj hij hw => ?_⟩
  · simp only [lay, List.length_cons, List.length_nil] at hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
    · exact hp.f_c
    · show (σ.sp - BitVec.ofNat 64 48).toNat + 48 ≤ 2 ^ 64
      have := hp.stk; have := σ.sp.isLt; bv_omega
    · exact hp.f_p
    · exact hp.f_p
    · exact hp.f_t
  · simp only [lay, List.length_cons, List.length_nil] at hi hj
    simp only [tWb, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
    simp only [Lay.buf, lay, Lay.size, List.getD_cons_zero, List.getD_cons_succ] <;>
    first | omega | skip
    all_goals first
      | exact hp.d_pt | exact hp.d_pt.symm | exact hp.d_pc | exact hp.d_pc.symm | exact hp.d_tc | exact hp.d_tc.symm
      | (rw [es]; exact hp.b_p) | (rw [es]; exact hp.b_p.symm) | (rw [es]; exact hp.b_t) | (rw [es]; exact hp.b_t.symm)
      | (rw [es]; exact hp.b_c) | (rw [es]; exact hp.b_c.symm)

/-! ## What holds throughout -/

/-- After the prologue, from the entry state `σ`. -/
structure KC (p : Params) (σ s : State) : Prop where
  site : Site (lay p σ) tWb 48 s
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  pres : ∀ r ∈ preserved, r ∉ savedTop → s.gpr r = σ.gpr r
  sav : TopSaved s.mem (σ.gpr .r5) σ
  pk : bytesAt s.mem ((lay p σ).A 3 0) p.pkLen = bytesAt σ.mem (σ.gpr .r3) p.pkLen

/-- After the hash. -/
structure KH (p : Params) (σ s : State) : Prop where
  site : Site (lay p σ) tWb 48 s
  sp : s.sp = σ.sp
  pres : ∀ r ∈ preserved, r ∉ savedTop → s.gpr r = σ.gpr r
  sav : TopSaved s.mem (σ.gpr .r5) σ
  tr : bytesAt s.mem ((lay p σ).A 4 0) 64 = Spec.MlDsa.pkTr (bytesAt σ.mem (σ.gpr .r3) p.pkLen)

theorem scr_ge {p : Params} (hp : PS p) : 32768 ≤ scrLen p ∧ scrLen p < 2 ^ 31 ∧ p.pkLen < 32768 := by
  rcases hp with rfl | rfl | rfl <;> decide

/-! ## The prologue -/

theorem saved_of {m : Mem} {P : Addr} {s₀ σ : State} (h : TopSaved m P s₀)
    (e : ∀ r ∈ savedTop, s₀.gpr r = σ.gpr r) (el : s₀.lr = σ.lr) : TopSaved m P σ :=
  ⟨h.s24.trans (e .r24 (by decide)), h.s25.trans (e .r25 (by decide)), h.s26.trans (e .r26 (by decide)),
    h.s27.trans (e .r27 (by decide)), h.s28.trans (e .r28 (by decide)), h.s29.trans (e .r29 (by decide)),
    h.s30.trans (e .r30 (by decide)), h.s31.trans (e .r31 (by decide)), h.slr.trans el⟩

theorem pro_ok {p : Params} (hp' : PS p) {σ : State} (hp : Pre p σ) : WP isa (.block pro) σ (KC p σ) := by
  have hL := lay_ok hp
  have fc := hp.f_c
  obtain ⟨hs1, hs2, hpk⟩ := scr_ge hp'
  have w0 : (lay p σ).buf 0 ∈ σ.wr := by
    rw [show (lay p σ).buf 0 = reg (σ.gpr .r5) (scrLen p) from rfl, hp.wr]
    exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have wS : ∀ {o n : Nat}, o + n ≤ 32768 → InRegions σ.wr (σ.gpr .r5 + BitVec.ofNat 64 o) n := fun {o n} h =>
    Lay.covers (L := lay p σ) (o := o) (l := n) w0 (by show o + n ≤ scrLen p; omega_arith) _ _
      ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  rw [pro, WP.block_append_iff, WP.block_append_iff]
  have h0 : WP isa (.block [mov .r6 .r5]) σ fun s₀ => s₀.gpr .r6 = σ.gpr .r5 ∧
      (∀ r, r ≠ .r6 → s₀.gpr r = σ.gpr r) ∧ s₀.lr = σ.lr ∧ s₀.mem = σ.mem ∧ s₀.rd = σ.rd ∧ s₀.wr = σ.wr ∧
      s₀.sp = σ.sp := by
    prun [Impl.Sha3.PPC64LE.Stream.mov]
    and_intros
    all_goals first
      | exact trivial
      | rfl
      | exact BitVec.add_zero _
      | (intro r hr; simp only [hr, ite_false])
  refine WP.mono h0 fun s₀ ⟨g6, g₀, lr₀, m₀, rd₀, wr₀, sp₀⟩ => ?_
  refine WP.mono (topSave_ok (.inl rfl) g6 fun o _ h₂ => by rw [wr₀]; exact wS (by omega_arith))
    fun s₁ ⟨sav, fr, g₁, lr₁, rd₁, wr₁, sp₁⟩ => ?_
  have g3 : s₁.gpr .r3 = σ.gpr .r3 := (g₁ _ (by decide)).trans (g₀ _ (by decide))
  have g4 : s₁.gpr .r4 = σ.gpr .r4 := (g₁ _ (by decide)).trans (g₀ _ (by decide))
  have g6' : s₁.gpr .r6 = σ.gpr .r5 := (g₁ _ (by decide)).trans g6
  have hmv : WP isa (.block [mov .r30 .r3, mov .r29 .r3, mov .r28 .r4, mov .r31 .r6, .li .r24 1]) s₁ fun s =>
      s.gpr .r30 = σ.gpr .r3 ∧ s.gpr .r29 = σ.gpr .r3 ∧ s.gpr .r28 = σ.gpr .r4 ∧ s.gpr .r31 = σ.gpr .r5 ∧
      (∀ r ∈ preserved, r ∉ savedTop → s.gpr r = s₁.gpr r) ∧
      s.mem = s₁.mem ∧ s.rd = s₁.rd ∧ s.wr = s₁.wr ∧ s.sp = s₁.sp := by
    prun [Impl.Sha3.PPC64LE.Stream.mov, g3, g4, g6', BitVec.add_zero]
    and_intros
    all_goals first
      | exact trivial
      | rfl
      | (intro r hr hs
         simp only [savedTop, List.mem_cons, List.not_mem_nil, or_false, not_or] at hs
         obtain ⟨a24, a25, a26, a27, a28, a29, a30, a31⟩ := hs
         simp only [a24, a28, a29, a30, a31, ite_false])
  have sav' : TopSaved s₁.mem (σ.gpr .r5) σ := by
    exact saved_of sav (fun r hr => g₀ r (by rintro rfl; simp [savedTop] at hr)) lr₀
  refine WP.mono hmv fun s ⟨g30, g29, g28, g31, cs, m, rd, wr, sp⟩ => ⟨⟨hL, rfl, by decide, by decide,
    by show 32768 ≤ scrLen p; omega_arith, rfl, by rw [sp, sp₁, sp₀]; rfl, by decide,
    by rw [sp, sp₁, sp₀]; exact hp.stk, g31, g30, g29, g28,
    fun i hi hi1 => ?_, fun i hi hi1 => ?_⟩, rd.trans (rd₁.trans rd₀), wr.trans (wr₁.trans wr₀),
    sp.trans (sp₁.trans sp₀),
    fun r hr hs => (cs r hr hs).trans ((g₁ r (by rintro rfl; simp [preserved] at hr)).trans
      (g₀ r (by rintro rfl; simp [preserved] at hr))), by rw [m]; exact sav', ?_⟩
  · show _ ∈ s.wr
    rw [wr, wr₁, wr₀, hp.wr]
    simp only [tWb, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · simp [Lay.buf, lay]
    · exact absurd rfl hi1
    · simp [Lay.buf, lay]
  · show _ ∈ s.rd ++ s.wr
    rw [rd, rd₁, rd₀, wr, wr₁, wr₀, hp.rd, hp.wr]
    rcases (by omega_arith : i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl <;> simp [Lay.buf, lay]
  · have e : (lay p σ).A 3 0 = σ.gpr .r3 := by simp only [Lay.A, BitVec.add_zero]; rfl
    rw [m, e, ← m₀]
    refine Proof.MlKem.bytesAt_frame fr (fun r hr => ?_) (by omega_arith)
    rw [List.mem_singleton] at hr; subst hr
    have e3 : (lay p σ).R 3 0 p.pkLen = ⟨σ.gpr .r3, p.pkLen⟩ := by simp only [Lay.R, BitVec.add_zero]; rfl
    rw [show saveR (σ.gpr .r5) = (lay p σ).R 0 840 72 from rfl, ← e3]
    exact disjW hL (i := 3) (o := 0) (l := p.pkLen) (j := 0) (o' := 840) (l' := 72)
      (by rcases hp' with rfl | rfl | rfl <;> rfl) (.inr (by decide))

theorem pro_piece {p : Params} (hp' : PS p) :
    Piece (Pre p) ptPub (fun σ s => s = σ) (KC p) (.block pro) :=
  ⟨fun σ s hp hs => by subst hs; exact pro_ok hp' hp,
    Sample.taint_block [.r3, .r4, .r5] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ => by
      subst h₁ h₂; exact pub.1)
      (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      obtain ⟨-, e0, e1, e2⟩ := pub
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [e0, e1, e2]) (by taint_decide)⟩

/-! ## Two runs -/

/-- Two runs in the layout of some entry state. -/
def TTwo (p : Params) (x y : State) : Prop := ∃ σ, Two (lay p σ) tWb 48 x y

theorem two_of {p : Params} {σ₁ σ₂ x y : State} (pub : ptPub σ₁ σ₂) (h₁ : Site (lay p σ₁) tWb 48 x)
    (h₂ : Site (lay p σ₂) tWb 48 y) (e₁ : x.sp = σ₁.sp) (e₂ : y.sp = σ₂.sp) : TTwo p x y :=
  ⟨σ₁, h₁, lay_pub pub ▸ h₂, by rw [e₁, e₂, pub.1]⟩

/-- Taint analysis from the pointer to `scratch`, in two runs in some layout. -/
theorem ttaint31 {p : Params} {c : Prog isa} {hc : VG.Taint.Hint VG.PPC64LE.taint.T}
    (h : (VG.PPC64LE.taint.check (Taint.ofRegs [.r31]) c hc).isSome = true) : RelCT isa (TTwo p) c fun _ _ => True :=
  RelCT.exists_ fun _ => taint31 (fun _ _ h => h) h

/-! ## The hash -/

/-- The buffers the sponge sees: all but the first copy of `pk`. -/
abbrev hK (i : Nat) : Bool := i != 2

theorem hK_ok : ∀ i < 5, ∀ j < 5, i ≠ j → 2 ≤ i → 2 ≤ j → hK i = true → hK j = true → i ∈ tWb ∨ j ∈ tWb :=
  fun i _ j _ hij _ _ hi hj => by
    simp only [hK, bne_iff_ne, ne_eq] at hi hj
    simp only [tWb, List.mem_cons, List.not_mem_nil, or_false]; omega

theorem trPieces {p : Params} (hp' : PS p) {σ s : State} (hs : Site (lay p σ) tWb 48 s) :
    (∀ pc ∈ ([⟨.r29, 0, p.pkLen⟩] : List Impl.MlKem.PPC64LE.Piece),
      PieceOk (hashLay (lay p σ) s hK) ix s false pc) ∧
    PieceOk (hashLay (lay p σ) s hK) ix s true (⟨.r28, 0, 64⟩ : Impl.MlKem.PPC64LE.Piece) := by
  obtain ⟨-, -, hpk⟩ := scr_ge hp'
  refine ⟨fun pc hpc => ?_, pieceS hs rfl (by decide) (by decide) (by decide)
    (by rcases hp' with rfl | rfl | rfl <;> rfl) (.inr rfl) fun _ => by decide⟩
  rw [List.mem_singleton] at hpc; subst hpc
  exact pieceS hs rfl (show (0 : Nat) < 32768 by decide) hpk (by rcases hp' with rfl | rfl | rfl <;> decide)
    (by rcases hp' with rfl | rfl | rfl <;> rfl) (.inr rfl) fun h => absurd h (by decide)

theorem hash_ok' {p : Params} (hp' : PS p) {σ s : State} (h : KC p σ s) : WP isa (trHash p) s (KH p σ) := by
  have hs := h.site
  obtain ⟨hin, hq⟩ := trPieces hp' hs
  unfold trHash
  refine WP.mono (hashS hs hK_ok (rate := 136) (sfx := 0x1f) (by decide) (by decide) (by simp) hin hq)
    fun s' ⟨k', o'⟩ => ⟨hs.kept k', k'.sp.trans h.sp, fun r hr hs' => (k'.cs r hr).trans (h.pres r hr hs'),
      h.sav.keep k'.frame (fun r hr => ?_), ?_⟩
  · have hL := hs.ok
    rw [show saveR (σ.gpr .r5) = (lay p σ).R 0 840 72 from rfl]
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl <;>
      exact disjW hL (by rcases hp' with rfl | rfl | rfl <;> rfl) (.inl (by decide))
  · have o₃ : bytesAt s'.mem ((lay p σ).A 4 0) 64 = _ := o'
    rw [o₃]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, Lay.pb,
      hashLay_ptr _ _ _ (ix_ne1 _)]
    have e : bytesAt s.mem ((lay p σ).ptr (ix Reg.r29) + BitVec.ofNat 64 0) p.pkLen =
        bytesAt σ.mem (σ.gpr .r3) p.pkLen := h.pk
    rw [e, shake31]
    exact (Proof.MlKem.shake256_eq _ _).symm

theorem hash_piece {p : Params} (hp' : PS p) : Piece (Pre p) ptPub (KC p) (KH p) (trHash p) :=
  ⟨fun _ _ _ h => hash_ok' hp' h,
    rel_of (RelCT.exists_ fun σ => hashS_tr (L := lay p σ) hK_ok (rate := 136) (sfx := 0x1f) (by decide)
      (by decide) (by simp) (fun s hs => (trPieces hp' hs).1) (fun s hs => (trPieces hp' hs).2) fun _ _ h => h)
      fun _ _ _ _ _ _ pub h₁ h₂ => two_of pub h₁.site h₂.site h₁.sp h₂.sp⟩

/-! ## The return -/

theorem epi_ok {p : Params} (hp' : PS p) {σ s : State} (h : KH p σ s) :
    WP isa (.block topEnd) s fun s' =>
      PPC64LE.target.abiPreserved σ s' ∧ (Spec.MlDsa.pkTrContract p PPC64LE.abi 48).post σ s' := by
  have hs := h.site
  obtain ⟨hs1, -, -⟩ := scr_ge hp'
  have hin : ∀ o, 840 ≤ o → o + 8 ≤ 912 → InRegions (s.rd ++ s.wr) (σ.gpr .r5 + BitVec.ofNat 64 o) 8 :=
    fun o h₁ h₂ => mem_rd_wr' (Lay.covers (L := lay p σ) (o := o) (l := 8) (hs.cw 0 (by decide) (by decide))
      (by show o + 8 ≤ scrLen p; omega_arith) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)
  refine WP.mono (topEnd_ok hs.r31 h.sav hin h.pres)
    fun s' ⟨pr, lr, _, m', sp', _, _⟩ => ⟨⟨pr, sp'.trans h.sp, lr⟩, ?_⟩
  sig_post [Spec.MlDsa.pkTrContract, Spec.MlDsa.pkTrSig, PPC64LE.abi, PPC64LE.argRegs]
  have e4 : σ.gpr .r4 = (lay p σ).A 4 0 := by simp only [Lay.A, BitVec.add_zero]; rfl
  rw [m', e4]
  exact h.tr

theorem epi_piece {p : Params} (hp' : PS p) :
    Piece (Pre p) ptPub (KH p)
      (fun σ s => PPC64LE.target.abiPreserved σ s ∧ (Spec.MlDsa.pkTrContract p PPC64LE.abi 48).post σ s)
      (.block topEnd) :=
  ⟨fun _ _ _ h => epi_ok hp' h, rel_of (ttaint31 (by taint_decide))
    fun _ _ _ _ _ _ pub h₁ h₂ => two_of pub h₁.site h₂.site h₁.sp h₂.sp⟩

/-! ## The function -/

theorem pkTr_piece {p : Params} (hp' : PS p) :
    Piece (Pre p) ptPub (fun σ s => s = σ)
      (fun σ s => PPC64LE.target.abiPreserved σ s ∧ (Spec.MlDsa.pkTrContract p PPC64LE.abi 48).post σ s)
      (pkTr p) :=
  (pro_piece hp').seq ((hash_piece hp').seq (epi_piece hp'))

/-- A state satisfying `pkTrContract`'s precondition. -/
def pkTrSat (p : Params) : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x10000 | _ => 0
  lr := 0
  sp := 0x80000
  mem _ := 0
  rd := [⟨0x1000, p.pkLen⟩]
  wr := [⟨0x2000, 64⟩, ⟨0x10000, scrLen p⟩]

theorem pkTr_verified (p : Params) (hp : PS p) (hsat : (Spec.MlDsa.pkTrContract p PPC64LE.abi 48).pre (pkTrSat p)) :
    Verified PPC64LE.target (pkTr p) (Spec.MlDsa.pkTrContract p PPC64LE.abi 48) := by
  have hk := pkTr_piece hp
  refine ⟨fun s hs => hk.ok s s (pre_of hs) rfl, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ⟨pkTrSat p, hsat⟩⟩
  sig_pub [Spec.MlDsa.pkTrContract, Spec.MlDsa.pkTrSig, PPC64LE.abi, PPC64LE.argRegs] at hpub
  obtain ⟨hsp, h3, h4, h5⟩ := hpub
  exact relStart hk.tr s₁ s₂ t₁ t₂ s₁' s₂' (pre_of h₁) (pre_of h₂) ⟨hsp, h3, h4, h5⟩ e₁ e₂

theorem pkTr44_sat : (Spec.MlDsa.pkTrContract mlDsa44 PPC64LE.abi 48).pre (pkTrSat mlDsa44) := by
  sig_sat_check [Spec.MlDsa.pkTrContract, Spec.MlDsa.pkTrSig, PPC64LE.abi, PPC64LE.argRegs, pkTrSat]
theorem pkTr65_sat : (Spec.MlDsa.pkTrContract mlDsa65 PPC64LE.abi 48).pre (pkTrSat mlDsa65) := by
  sig_sat_check [Spec.MlDsa.pkTrContract, Spec.MlDsa.pkTrSig, PPC64LE.abi, PPC64LE.argRegs, pkTrSat]
theorem pkTr87_sat : (Spec.MlDsa.pkTrContract mlDsa87 PPC64LE.abi 48).pre (pkTrSat mlDsa87) := by
  sig_sat_check [Spec.MlDsa.pkTrContract, Spec.MlDsa.pkTrSig, PPC64LE.abi, PPC64LE.argRegs, pkTrSat]

theorem pkTr44_verified : Verified PPC64LE.target (pkTr mlDsa44) (Spec.MlDsa.pkTrContract mlDsa44 PPC64LE.abi 48) :=
  pkTr_verified _ (.inl rfl) pkTr44_sat
theorem pkTr65_verified : Verified PPC64LE.target (pkTr mlDsa65) (Spec.MlDsa.pkTrContract mlDsa65 PPC64LE.abi 48) :=
  pkTr_verified _ (.inr (.inl rfl)) pkTr65_sat
theorem pkTr87_verified : Verified PPC64LE.target (pkTr mlDsa87) (Spec.MlDsa.pkTrContract mlDsa87 PPC64LE.abi 48) :=
  pkTr_verified _ (.inr (.inr rfl)) pkTr87_sat

end VG.Proof.MlDsa.PPC64LE.PkTr

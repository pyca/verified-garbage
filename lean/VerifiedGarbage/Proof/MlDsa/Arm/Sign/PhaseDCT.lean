module

public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseD
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseA
import VerifiedGarbage.Proof.Sha3.Arm.Permute
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Call
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Blocks
import VerifiedGarbage.Proof.MlKem.Arm.CallsCT
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Call
meta import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Blocks
meta import VerifiedGarbage.Proof.MlKem.Arm.CallsCT
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData

/-! ### `MlDsa.Arm.Sign.Rel`, which this module and modules that import it used -/

section

/-! ### `MlDsa.Arm.Sign.CopyTr`, which the modules that import this one used -/

section

/-!
# ML-DSA signing on ARMv7: copies leak only their addresses

The setup of a copy accesses no memory, and its loop leaks only the pointers
and the count in `r0`–`r2` (by the taint analysis), so two runs of a copy
between the same addresses leak the same (`copy_tr`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign

theorem copySetup_nomem (dst src : Ptr) (n : Nat) :
    ∀ i ∈ lea .r0 src ++ lea .r1 dst ++ movi .r2 n, ∀ s, isa.addrs i s = [] := by
  intro i hi s
  simp only [lea, movi, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Two runs of a copy from the same addresses leak the same. -/
theorem copy_tr {dst src : Ptr} {n : Nat} (b1 : src.1 ∈ bases) (b2 : dst.1 ∈ bases) {P : State → State → Prop}
    (hP : ∀ x y, P x y → x.gpr dst.1 = y.gpr dst.1 ∧ x.gpr src.1 = y.gpr src.1) :
    RelCT isa P (copy dst src n) fun _ _ => True := by
  unfold copy
  refine RelCT.seq (R := fun (x y : State) => ∀ r ∈ [Reg.r0, .r1, .r2], x.gpr r = y.gpr r)
    (postDep (block_nomem_tr (copySetup_nomem dst src n))
      (fun x y _ => ⟨copySetup_ok b1 b2 x, copySetup_ok b1 b2 y⟩)
      fun x y x' y' hp ⟨a0, a1, a2, _⟩ ⟨c0, c1, c2, _⟩ => ?_)
    (VG.Proof.MlKem.Arm.taint_prog [.r0, .r1, .r2] (fun _ _ h => h) (by native_taint_decide))
  obtain ⟨e1, e2⟩ := hP x y hp
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [a0, c0, e2]
  · rw [a1, c1, e1]
  · rw [a2, c2]

end VG.Proof.MlDsa.Arm.Sign

end

end

/-!
# ML-DSA signing on ARMv7: two runs

Constant time is proven piece by piece (`RelCT`) for two runs from entry
states that satisfy `signK`'s precondition and agree on its public data, each
satisfying the invariant `I` of the correctness proof, and related by `E`
(`RR`): each piece leaks the same, correctness gives each run's next
invariant, and the piece's own proof the next relation (`relInvE`). The runs
are in the same layout (`RR.lrel`) and agree on `ρ` (`RR.rho`), which the
leakage begins with.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- Two states each related by `I` to an entry state; the entry states
satisfy `Pre` and agree by `Pub`. -/
def Rel2 (Pre : State → Prop) (Pub : State → State → Prop) (I : State → State → Prop) (s₁ s₂ : State) : Prop :=
  ∃ σ₁ σ₂, Pre σ₁ ∧ Pre σ₂ ∧ Pub σ₁ σ₂ ∧ I σ₁ s₁ ∧ I σ₂ s₂

/-- Two runs, each satisfying `I` from its entry state, related by `E`. -/
def RR (p : Params) (D : Nat) (I E : State → State → Prop) (x y : State) : Prop :=
  Rel2 (signK p D).pre (signK p D).pub I x y ∧ E x y

section
variable {p : Params} {D : Nat}

theorem relInvE {I J E E' : State → State → Prop} {c : Prog isa}
    (hw : ∀ σ s, (signK p D).pre σ → I σ s → WP isa c s (J σ))
    (ht : RelCT isa (RR p D I E) c E') : RelCT isa (RR p D I E) c (RR p D J E') := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  obtain ⟨ht', he⟩ := ht _ _ _ _ _ _ hr e₁ e₂
  obtain ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩, _⟩ := hr
  obtain ⟨_, u₁, f₁, g₁⟩ := hw σ₁ s₁ p₁ i₁
  obtain ⟨_, u₂, f₂, g₂⟩ := hw σ₂ s₂ p₂ i₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht', ⟨σ₁, σ₂, p₁, p₂, hpub, g₁, g₂⟩, he⟩

theorem RR.lrel {I E : State → State → Prop} (hI : ∀ σ s, I σ s → St p D σ s) {x y : State}
    (h : RR p D I E x y) : LRel D (sgR p) (sgW p) x y := by
  obtain ⟨⟨σ₁, σ₂, _, _, hpub, i₁, i₂⟩, _⟩ := h
  have S₁ := hI _ _ i₁
  have S₂ := hI _ _ i₂
  obtain ⟨h1, h2, h3, h4, h5, h6, _⟩ := hpub
  refine ⟨S₁.lay, S₂.lay, fun b hb => ?_, by rw [S₁.top.sp, S₂.top.sp, h6]⟩
  have r₁ := S₁.top.regs
  have r₂ := S₂.top.regs
  simp only [sgR, sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · rw [r₁ .r4 (by decide), r₂ .r4 (by decide)]; exact h1
  · rw [r₁ .r5 (by decide), r₂ .r5 (by decide)]; exact h2
  · rw [r₁ .r6 (by decide), r₂ .r6 (by decide)]; exact h3
  · rw [r₁ .r7 (by decide), r₂ .r7 (by decide)]; exact h5
  · rw [r₁ .r8 (by decide), r₂ .r8 (by decide)]; exact h4

theorem WP.conj {c : Prog isa} {s : State} {Q₁ Q₂ : State → Prop} (h₁ : WP isa c s Q₁) (h₂ : WP isa c s Q₂) :
    WP isa c s fun s' => Q₁ s' ∧ Q₂ s' := by
  obtain ⟨t, s', e, q₁⟩ := h₁
  obtain ⟨_, _, e', q₂⟩ := h₂
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact ⟨t, _, e, q₁, q₂⟩

/-- A piece that takes each run from `I` to `J` and from `s` to `s'` with
`F s s'`, and leaks the same from runs related by `RR p D I E`, with `Q₀` of
the final states. -/
theorem stepRR {I J E E' Q₀ F : State → State → Prop} {c : Prog isa}
    (hw : ∀ σ s, (signK p D).pre σ → I σ s → WP isa c s fun s' => J σ s' ∧ F s s')
    (ht : RelCT isa (RR p D I E) c Q₀)
    (hE : ∀ x y x' y', RR p D I E x y → F x x' → F y y' → Q₀ x' y' → E' x' y') :
    RelCT isa (RR p D I E) c (RR p D J E') := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  obtain ⟨ht', hq⟩ := ht _ _ _ _ _ _ hr e₁ e₂
  obtain ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩, he⟩ := hr
  obtain ⟨_, u₁, f₁, g₁, k₁⟩ := hw σ₁ s₁ p₁ i₁
  obtain ⟨_, u₂, f₂, g₂, k₂⟩ := hw σ₂ s₂ p₂ i₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht', ⟨σ₁, σ₂, p₁, p₂, hpub, g₁, g₂⟩, hE _ _ _ _ ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩, he⟩ k₁ k₂ hq⟩

end

/-! ## Runs related through their entry states -/

/-- Two runs, each satisfying `I` from its entry state, the entry states related by `E`. -/
def RS (p : Params) (D : Nat) (E I : State → State → Prop) (x y : State) : Prop :=
  ∃ σ₁ σ₂, (signK p D).pre σ₁ ∧ (signK p D).pre σ₂ ∧ (signK p D).pub σ₁ σ₂ ∧ E σ₁ σ₂ ∧ I σ₁ x ∧ I σ₂ y

section
variable {p : Params} {D : Nat}

theorem lrel_of {σ₁ σ₂ x y : State} (hpub : (signK p D).pub σ₁ σ₂) (S₁ : St p D σ₁ x) (S₂ : St p D σ₂ y) :
    LRel D (sgR p) (sgW p) x y := by
  obtain ⟨h1, h2, h3, h4, h5, h6, _⟩ := hpub
  refine ⟨S₁.lay, S₂.lay, fun b hb => ?_, by rw [S₁.top.sp, S₂.top.sp, h6]⟩
  have r₁ := S₁.top.regs
  have r₂ := S₂.top.regs
  simp only [sgR, sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · rw [r₁ .r4 (by decide), r₂ .r4 (by decide)]; exact h1
  · rw [r₁ .r5 (by decide), r₂ .r5 (by decide)]; exact h2
  · rw [r₁ .r6 (by decide), r₂ .r6 (by decide)]; exact h3
  · rw [r₁ .r7 (by decide), r₂ .r7 (by decide)]; exact h5
  · rw [r₁ .r8 (by decide), r₂ .r8 (by decide)]; exact h4

theorem RS.lrel {E I : State → State → Prop} (hI : ∀ σ s, I σ s → St p D σ s) {x y : State}
    (h : RS p D E I x y) : LRel D (sgR p) (sgW p) x y := by
  obtain ⟨σ₁, σ₂, _, _, hpub, _, i₁, i₂⟩ := h
  exact lrel_of hpub (hI _ _ i₁) (hI _ _ i₂)

theorem RS.mono {E I E' I' : State → State → Prop} {x y : State} (h : RS p D E I x y)
    (hE : ∀ σ₁ σ₂, E σ₁ σ₂ → E' σ₁ σ₂) (hI : ∀ σ s, I σ s → I' σ s) : RS p D E' I' x y := by
  obtain ⟨σ₁, σ₂, p₁, p₂, hpub, e, i₁, i₂⟩ := h
  exact ⟨σ₁, σ₂, p₁, p₂, hpub, hE _ _ e, hI _ _ i₁, hI _ _ i₂⟩

/-- A piece that leaks the same from two runs in the layout that satisfy `T`, and takes each run from
`I` to `J`. -/
theorem liftL {E I J : State → State → Prop} {T : State → Prop} {c : Prog isa}
    (hI : ∀ σ s, I σ s → St p D σ s ∧ T s) (hw : ∀ σ s, (signK p D).pre σ → I σ s → WP isa c s (J σ))
    (ht : RelCT isa (fun x y => LRel D (sgR p) (sgW p) x y ∧ T x ∧ T y) c fun _ _ => True) :
    RelCT isa (RS p D E I) c (RS p D E J) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  obtain ⟨σ₁, σ₂, p₁, p₂, hpub, he, i₁, i₂⟩ := hr
  obtain ⟨ht', -⟩ := ht _ _ _ _ _ _ ⟨lrel_of hpub (hI _ _ i₁).1 (hI _ _ i₂).1, (hI _ _ i₁).2, (hI _ _ i₂).2⟩ e₁ e₂
  obtain ⟨_, u₁, f₁, g₁⟩ := hw σ₁ s₁ p₁ i₁
  obtain ⟨_, u₂, f₂, g₂⟩ := hw σ₂ s₂ p₂ i₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht', σ₁, σ₂, p₁, p₂, hpub, he, g₁, g₂⟩

/-- `liftL`, with a leakage proof from any relation the runs satisfy. -/
theorem liftR {E I J : State → State → Prop} {c : Prog isa}
    (hw : ∀ σ s, (signK p D).pre σ → I σ s → WP isa c s (J σ))
    (ht : RelCT isa (RS p D E I) c fun _ _ => True) : RelCT isa (RS p D E I) c (RS p D E J) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  obtain ⟨ht', -⟩ := ht _ _ _ _ _ _ hr e₁ e₂
  obtain ⟨σ₁, σ₂, p₁, p₂, hpub, he, i₁, i₂⟩ := hr
  obtain ⟨_, u₁, f₁, g₁⟩ := hw σ₁ s₁ p₁ i₁
  obtain ⟨_, u₂, f₂, g₂⟩ := hw σ₂ s₂ p₂ i₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht', σ₁, σ₂, p₁, p₂, hpub, he, g₁, g₂⟩

/-- Two pieces in sequence, from two runs in the layout that satisfy `I` (what the first piece needs),
each piece leaving the layout. -/
theorem seqL {c₁ c₂ : Prog isa} {I J : State → Prop} {Q : State → State → Prop}
    (h₁ : RelCT isa (fun x y => LRel D (sgR p) (sgW p) x y ∧ I x ∧ I y) c₁ fun _ _ => True)
    (w₁ : ∀ x, Lay D (sgR p) (sgW p) x → I x → WP isa c₁ x fun x' => (∃ W, PostB D x x' W) ∧ J x')
    (h₂ : RelCT isa (fun x y => LRel D (sgR p) (sgW p) x y ∧ J x ∧ J y) c₂ Q) :
    RelCT isa (fun x y => LRel D (sgR p) (sgW p) x y ∧ I x ∧ I y) (.seq c₁ c₂) Q :=
  RelCT.seq (postDep h₁ (F := fun x x' => (∃ W, PostB D x x' W) ∧ J x')
    (fun x y h => ⟨w₁ x h.1.lx h.2.1, w₁ y h.1.ly h.2.2⟩)
    fun _ _ _ _ h ⟨⟨_, hx⟩, jx⟩ ⟨⟨_, hy⟩, jy⟩ => ⟨h.1.post (sgB_bases p) hx hy, jx, jy⟩) h₂

end

/-! ## `ρ` -/

theorem signLeak_head (p : Params) (sk μ rnd : List Byte) :
    ∃ X, signLeak p sk μ rnd = leakBytes (sk.take 32) ++ X := by
  unfold signLeak
  rcases e : skDecode p sk with ⟨ρ, K, tr, s₁, s₂, t₀⟩
  have hρ : ρ = sk.take 32 := by rw [← skRho_eq p sk, e]
  subst hρ
  exact ⟨_, rfl⟩

theorem leak_rho {p : Params} {sk₁ sk₂ μ₁ μ₂ r₁ r₂ : List Byte} (h1 : sk₁.length = p.skLen)
    (h2 : sk₂.length = p.skLen) (h : signLeak p sk₁ μ₁ r₁ = signLeak p sk₂ μ₂ r₂) :
    sk₁.take 32 = sk₂.take 32 := by
  obtain ⟨X₁, e₁⟩ := signLeak_head p sk₁ μ₁ r₁
  obtain ⟨X₂, e₂⟩ := signLeak_head p sk₂ μ₂ r₂
  rw [e₁, e₂] at h
  refine leakBytes_inj (List.append_inj h ?_).1
  rw [leakBytes_length, leakBytes_length, List.length_take, List.length_take, h1, h2]

theorem pub_rho {p : Params} {D : Nat} {σ₁ σ₂ : State} (h : (signK p D).pub σ₁ σ₂) :
    rhoOf p σ₁ = rhoOf p σ₂ :=
  leak_rho (VG.Proof.MlKem.bytesAt_length _ _ _) (VG.Proof.MlKem.bytesAt_length _ _ _) h.2.2.2.2.2.2.1

end VG.Proof.MlDsa.Arm.Sign

end

end

/-!
# ML-DSA signing on ARMv7: decoding leaks only the pointers

Each call while decoding leaks only its pointers, given that its input
polynomial is reduced (`dec_tr`); so two runs agree on what decoding leaks
(`decode_tr`); and copying prepared polynomials leaks only the pointers too
(`decodeC_tr`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- A piece that leaks only its pointers, from runs in the layout. -/
theorem liftT {p : Params} {D : Nat} {E I J : State → State → Prop} {c : Prog isa}
    (hI : ∀ σ s, I σ s → St p D σ s) (hw : ∀ σ s, (signK p D).pre σ → I σ s → WP isa c s (J σ))
    (ht : RelCT isa (LRel D (sgR p) (sgW p)) c fun _ _ => True) : RelCT isa (RS p D E I) c (RS p D E J) :=
  liftL (T := fun _ => True) (fun σ s h => ⟨hI σ s h, trivial⟩) hw (RelCT.mono ht (fun _ _ h => h.1) fun _ _ h => h)

theorem dec_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {a b c : Nat} {src : Ptr} {len x y j : Nat}
    (hp : (x, y) ∈ bitPackParams) (hl : len = 32 * bitlen (x + y)) (hc : decChk p a b c src len j = true) :
    RelCT isa (LRel D (sgR p) (sgW p)) (.seq (bitUnpackAt P src len x y (pS j)) (nttAt P (pS j))) fun _ _ => True := by
  simp only [decChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨h1, h2⟩, _⟩, _⟩ := hc
  refine RelCT.mono (seqL (p := p) (I := fun _ => True) (J := fun s => Reduced s.mem (pa s (pS j)))
    (RelCT.mono (bupAt_tr hP hp hl h1) (fun _ _ h => h.1) fun _ _ h => h)
    (fun s L _ => WP.mono (bupAt_ok hP L hp hl h1) fun s' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, by rw [hP'.pa (pS_bases _)]; exact hq.1⟩)
    (ipAt_tr (t := ntt) hP.ntt h2)) (fun _ _ h => ⟨h, trivial, trivial⟩) fun _ _ h => h

theorem decode_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hc : dChk p = true) {E : State → State → Prop} :
    RelCT isa (RS p D E (IM p D)) (decode P p) (RS p D E (IK p D)) := by
  have hs := dChk_spec hc
  unfold decode
  refine RelCT.seq (R := RS p D E fun σ s => ID p D σ p.ℓ 0 0 s) ?_ (RelCT.seq (R := RS p D E fun σ s => ID p D σ p.ℓ p.k 0 s)
    ?_ (RelCT.seq (R := RS p D E fun σ s => ID p D σ p.ℓ p.k p.k s) ?_ ?_))
  · refine RelCT.mono (seqR_tr (R := fun r => RS p D E fun σ s => ID p D σ r 0 0 s) p.ℓ 0 fun r _ hr =>
      liftT (fun _ _ h => h.im.st) (fun _ _ _ h => decS1_ok hP hc (by omega_using [hr]) h)
        (dec_tr hP hs.2.2.2.2.2.2.1 (sLen_eq p) (hs.1 r (by omega_using [hr])).1)) (fun x y h => h.mono (fun _ _ h => h) fun _ _ h =>
          ⟨h, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
            fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun x y h => by rwa [Nat.zero_add] at h
  · refine RelCT.mono (seqR_tr (R := fun i => RS p D E fun σ s => ID p D σ p.ℓ i 0 s) p.k 0 fun i _ hi =>
      liftT (fun _ _ h => h.im.st) (fun _ _ _ h => decS2_ok hP hc (by omega_using [hi]) h)
        (dec_tr hP hs.2.2.2.2.2.2.1 (sLen_eq p) (hs.2.1 i (by omega_using [hi])).1)) (fun x y h => h.mono (fun _ _ h => h) fun _ _ h =>
          ⟨h.im, h.s1, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩)
      fun x y h => by rwa [Nat.zero_add] at h
  · refine RelCT.mono (seqR_tr (R := fun i => RS p D E fun σ s => ID p D σ p.ℓ p.k i s) p.k 0 fun i _ hi =>
      liftT (fun _ _ h => h.im.st) (fun _ _ _ h => decT0_ok hP hc (by omega_using [hi]) h)
        (dec_tr hP (by decide) (by decide) (hs.2.2.1 i (by omega_using [hi])).1)) (fun x y h => h.mono (fun _ _ h => h) fun _ _ h =>
          ⟨h.im, h.s1, h.s2, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun x y h => by rwa [Nat.zero_add] at h
  · exact liftT (fun _ _ h => h.im.st) (fun _ _ _ h => rpp_ok hP hc h)
      (RelCT.mono (shake_tr (sgB_bases p) hP.hD hs.2.2.2.1) (fun _ _ h => h) fun _ _ _ => trivial)

/-- Two runs keep the same pointers in `bases`. -/
theorem rs_reg {p : Params} {D : Nat} {E I : State → State → Prop} (hI : ∀ σ s, I σ s → St p D σ s) {x y : State}
    (h : RS p D E I x y) {r : Reg} (hr : r ∈ bases) : x.gpr r = y.gpr r := by
  obtain ⟨σ₁, σ₂, _, _, hpub, _, i₁, i₂⟩ := h
  obtain ⟨h1, h2, h3, h4, h5, -, -, h9⟩ := hpub
  rw [(hI _ _ i₁).top.regs r hr, (hI _ _ i₂).top.regs r hr]
  simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [ptrOf] <;> with_reducible assumption

theorem decodeC_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hd : dChk p = true)
    (hc : dcChk p = true) {E : State → State → Prop} :
    RelCT isa (RS p D E (IM p D)) (decodeC P p) (RS p D E (IK p D)) := by
  have hs := dChk_spec hd
  have him0 : imChk p [] = true := by
    simp only [dcChk, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨-, -⟩, h0⟩, -⟩, -⟩, -⟩, -⟩ := hc
    exact h0
  unfold decodeC
  refine RelCT.seq (R := RS p D E fun σ s => IM p D σ s ∧ s.z = (stackArg σ 1 == 0)) ?_ (RelCT.ite ?_ ?_ ?_)
  · refine liftR (fun σ s _ h => WP.mono (cmp9_ok s D) fun s₁ ⟨hP₁, _, _, hz⟩ => ⟨h.step hP₁ him0, ?_⟩)
      (block_nomem_tr fun i hi s => by simp only [List.mem_singleton] at hi; subst hi; rfl)
    have e := h.st.top.regs .r9 (by decide)
    simp only [ptrOf] at e
    rw [hz, e]
  · rintro x y ⟨σ₁, σ₂, -, -, hpub, -, ⟨-, hx⟩, ⟨-, hy⟩⟩
    show some (!x.z) = some (!y.z)
    rw [hx, hy, hpub.2.2.2.2.2.2.2]
  · unfold cached
    refine RelCT.mono (P := RS p D E fun σ s => IM p D σ s ∧ stackArg σ 1 ≠ 0)
      (RelCT.seq (R := RS p D E fun σ s => ID p D σ p.ℓ p.k p.k s) ?_ ?_) ?_ fun _ _ h => h
    · exact liftR (fun σ s hpre ⟨h, hne⟩ => cachedCopy_ok hc hpre hne h)
        (copy_tr (by decide) (pS_bases _) fun x y h =>
          ⟨rs_reg (fun _ _ h => h.1.st) h (pS_bases _), rs_reg (fun _ _ h => h.1.st) h (by decide)⟩)
    · exact liftT (fun _ _ h => h.im.st) (fun _ _ _ h => rpp_ok hP hd h)
        (RelCT.mono (shake_tr (sgB_bases p) hP.hD hs.2.2.2.1) (fun _ _ h => h) fun _ _ _ => trivial)
    · rintro x y ⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, ⟨i₁, hx⟩, ⟨i₂, hy⟩⟩, hcx⟩
      have hcx' : some (!x.z) = some true := hcx
      rw [hx] at hcx'
      have hne : stackArg σ₁ 1 ≠ 0 := by simpa using hcx'
      exact ⟨σ₁, σ₂, p₁, p₂, hpub, he, ⟨i₁, hne⟩, ⟨i₂, hpub.2.2.2.2.2.2.2 ▸ hne⟩⟩
  · exact RelCT.mono (decode_tr hP hd) (fun x y ⟨h, _⟩ => h.mono (fun _ _ h => h) fun _ _ h => h.1)
      fun _ _ h => h

end VG.Proof.MlDsa.Arm.Sign

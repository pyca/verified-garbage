module

public import VerifiedGarbage.Impl.MlDsa.Arm.KeyGen.Frag
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Site
import VerifiedGarbage.Proof.MlKem.Arm.CallsCT
public import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Call
import VerifiedGarbage.Proof.MlKem.Arm.Loops
import VerifiedGarbage.Proof.MlDsa.Verify.Mem

/-! ### `MlDsa.Arm.KeyGen.Steps`, which the modules that import this one used -/

section

/-!
# ML-DSA on 32-bit ARM: bytes, copies and the sponge in the buffers of a `Site`

A byte stored (`setB_ok`), bytes copied (`copyS`, from ML-KEM's `copy_loop`),
and the sponge (`hashS`, from ML-KEM's `hash_ok`), with what they change as
triples of the layout.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Impl.MlKem.Arm (Piece hash copy copyBody)
open VG.Spec.Sha3 (bytesAt squeezeFrom absorb pad rates)
open VG.Proof.MlKem.Arm (PieceOk Outs)

/-- The byte `v` moved by `movw` and stored by `strb`. -/
theorem byte16 (v : Nat) : ((BitVec.ofNat 16 v).setWidth 32).setWidth 8 = BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_using []

section
variable {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (hs : Site L Wb STK s)
include hs

/-! ## A byte -/

theorem setB_ok {q : Ptr} (pq : PtrIn L q 1) (hw : ix q.1 ∈ Wb) (ho : q.2 < 4096) (v : Nat) :
    WP isa (.block (setB q v)) s fun s' =>
      Kept (L.RL [tri q 1]) s s' ∧ bytesAt s'.mem (lpa L q) 1 = [BitVec.ofNat 8 v] := by
  have gb := hs.val pq.1
  simp only [argVal] at gb
  have ea := hs.addrE pq (by decide)
  have hi : InRegions s.wr (State.addr (s.gpr q.1 + BitVec.ofNat 32 q.2)) 1 := by
    rw [gb, ea]; exact hs.cwE pq hw _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  have n12 : q.1 ≠ .r12 := by
    have := pq.1; simp only [argOk, Bool.or_eq_true, beq_iff_eq] at this
    rcases this with ((h | h) | h) | h <;> rw [h] <;> decide
  have n12' : ¬ q.1 = .r12 := n12
  rw [gb, ea] at hi
  run_block [setB, hi, ho, n12', gb, ea]
  refine ⟨⟨fun r hr hl => ?_, rfl, rfl, rfl, ?_⟩, ?_⟩
  · have : r ≠ .r12 := by revert r; decide
    simp only [this, ite_false]
  · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · rw [show ∀ (m : Mem) (a : Addr), bytesAt m a 1 = [m a] from fun _ _ => by simp [bytesAt], VG.WriteBytes.writeW8_apply,
      ite_eq_left rfl, byte16 v]

omit hs in
/-- A register of the layout is callee-saved (and not `lr`). -/
theorem base_pres {r : Reg} (h : argOk (.ptr (r, 0)) = true) : r ∈ preserved ∧ r ≠ .lr := by
  simp only [argOk, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((rfl | rfl) | rfl) | rfl <;> decide

/-! ## A copy -/

theorem copyS {sb db : Reg} {so dO len : Nat} (ps : PtrIn L (sb, so) len) (pd : PtrIn L (db, dO) len)
    (wd : ix db ∈ Wb) (hse : encodable (BitVec.ofNat 32 so) = true) (hde : encodable (BitVec.ofNat 32 dO) = true)
    (hle : encodable (BitVec.ofNat 32 len) = true) (hlen : len < 2 ^ 32) (hl0 : 0 < len)
    (hd : sepB L.sizes (tri (sb, so) len) (tri (db, dO) len) = true) :
    WP isa (copy sb so db dO len) s fun s' =>
      Kept (L.RL [tri (db, dO) len]) s s' ∧ bytesAt s'.mem (lpa L (db, dO)) len = bytesAt s.mem (lpa L (sb, so)) len := by
  have gs := hs.val ps.1
  have gd := hs.val pd.1
  simp only [argVal] at gs gd
  obtain ⟨ea, fa⟩ := hs.addr ps.2 hl0
  obtain ⟨eb, fb⟩ := hs.addr pd.2 hl0
  refine WP.seq (WP.mono (copy_setup (base_pres (by simpa [argOk] using ps.1))
    (base_pres (by simpa [argOk] using pd.1)) hse hde hle) fun s₁ ⟨o₁, g0, g1, g2⟩ => ?_)
  rw [gs] at g0; rw [gd] at g1
  have hdj := hs.dE hd (.inr wd)
  refine WP.mono (copy_loop fa fb hlen hl0 (by rw [ea, eb]; exact hdj)
    (by rw [ea, o₁.rd, o₁.wr]; exact hs.crE ps)
    (by rw [eb, o₁.wr]; exact hs.cwE pd wd) g0 g1 g2)
    fun s' ⟨cs, rd, wr, sp, fr, hb⟩ => ⟨?_, ?_⟩
  · refine (o₁.kept _).trans ⟨fun r hr _ => cs r hr, sp, rd, wr, ?_⟩
    rw [eb] at fr; exact fr
  · rw [eb, ea, o₁.mem] at hb; exact hb

/-! ## The sponge -/

omit hs in
theorem ix_ne1 (r : Reg) : ix r ≠ 1 := by cases r <;> decide

theorem hashS {K : Nat → Bool}
    (hK : ∀ i < 5, ∀ j < 5, i ≠ j → 2 ≤ i → 2 ≤ j → K i = true → K j = true → i ∈ Wb ∨ j ∈ Wb)
    {rate sfx : Nat} (hrate : rate ∈ rates) (hre : encodable (BitVec.ofNat 32 rate) = true)
    (hse : encodable (BitVec.ofNat 32 sfx) = true) (hsfx : sfx < 256) {ins : List Piece} {q : Piece} (hne : ins ≠ [])
    (hin : ∀ p ∈ ins, PieceOk (hashLay L s K) ix s false p) (hq : PieceOk (hashLay L s K) ix s true q) :
    WP isa (hash rate sfx ins [q]) s fun s' =>
      Kept (L.RL [(0, 0, 200), (0, 200, 640), (1, 0, STK), (ix q.base, q.off, q.len)]) s s' ∧
      bytesAt s'.mem (L.A (ix q.base) q.off) q.len = squeezeFrom rate (absorb rate
        (pad rate (BitVec.ofNat 8 sfx) (ins.map ((hashLay L s K).pb ix s.mem)).flatten)) 0 q.len := by
  refine WP.mono (hash_ok hrate hre hse hsfx (hs.ctx hK) hne hin (fun p hp => by
    rw [List.mem_singleton] at hp; subst hp; exact hq) (List.pairwise_singleton _ _)) fun s' ⟨k, o⟩ => ⟨?_, ?_⟩
  · refine ⟨k.cs, k.sp, k.rd, k.wr, k.frame.sub fun r hr => ?_⟩
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., by rw [hashLay_R L s K (by decide)]; exact fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by
        rw [hashLay_R L s K (by decide)]; exact fun _ h => h⟩
    · refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), ?_⟩
      have := hs.belowSub (n := 8) hs.s8
      intro x hx
      apply this
      have := hs.spk; have := hs.s8
      have := addr_toNat' s.sp
      have := addr_toNat' (s.sp - BitVec.ofNat 32 8)
      simp only [Region.Contains, hashLay, ite_true] at hx ⊢
      bv_omega
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))), by
        rw [hashLay_R L s K (ix_ne1 _)]; exact fun _ h => h⟩
  · have := o.1
    simp only [Lay.pb, hashLay_ptr L s K (ix_ne1 _)] at this
    exact this

/-- A piece of the sponge, in a buffer of the layout. -/
theorem pieceS {K : Nat → Bool} {w : Bool} {p : Piece} (hb : argOk (.ptr (p.base, 0)) = true)
    (hoe : encodable (BitVec.ofNat 32 p.off) = true) (hle : encodable (BitVec.ofNat 32 p.len) = true)
    (hpos : 0 < p.len) (hlt : p.off + p.len < 2 ^ 32)
    (hsep : sepAll (hashLay L s K).sizes (ix p.base, p.off, p.len) kRegs = true)
    (hK : ix p.base = 0 ∨ K (ix p.base) = true) (hw : w = true → ix p.base ∈ Wb) :
    PieceOk (hashLay L s K) ix s w p := by
  have hi5 : ix p.base < 5 := by
    simp only [argOk, Bool.or_eq_true, beq_iff_eq] at hb
    rcases hb with ((h | h) | h) | h <;> rw [h] <;> decide
  have e := hashLay_size L s (ix_ne1 p.base) hK hi5
  refine ⟨base_pres hb, by rw [hashLay_ptr L s K (ix_ne1 _)]; exact hs.base hb, hoe, hle, hpos, hlt, hsep, ?_⟩
  rw [hashLay_ptr L s K (ix_ne1 _), e]
  cases w with
  | true => exact hs.cw _ (hw rfl) (ix_ne1 _)
  | false => exact hs.cr _ hi5 (ix_ne1 _)

end

/-! ## What a part keeps -/

section
variable {L : Lay} {Wb : List Nat} (hL : OkW L Wb) {W : List (Nat × Nat × Nat)} {m m' : Mem}
  (hf : Frame (L.RL W) m m') {i o l : Nat} (h : sepAll L.sizes (i, o, l) W = true) (hw : i ∈ Wb)
include hL hf h hw

omit hf in
theorem keepD : ∀ r ∈ L.RL W, (L.R i o l).Disjoint r := fun r hr => by
  obtain ⟨w, hw', rfl⟩ := List.mem_map.mp hr
  exact disjW hL (List.all_eq_true.mp h w hw') (.inl hw)

theorem bytes_keepW (hl : l ≤ 2 ^ 64) : bytesAt m' (L.A i o) l = bytesAt m (L.A i o) l :=
  Proof.MlKem.bytesAt_frame hf (keepD hL h hw) hl

section
variable (hl : l = 1024)
include hl

theorem polyIs_keepW {f : Spec.MlDsa.Poly} (hp : Proof.MlDsa.PolyIs m (L.A i o) f) : Proof.MlDsa.PolyIs m' (L.A i o) f :=
  Proof.MlDsa.Verify.polyIs_frame hf (fun r hr => by have := keepD hL h hw r hr; subst hl; exact this) hp

theorem reduced_keepW (hp : Proof.MlDsa.Reduced m (L.A i o)) : Proof.MlDsa.Reduced m' (L.A i o) :=
  Proof.MlDsa.Verify.reduced_frame hf (fun r hr => by have := keepD hL h hw r hr; subst hl; exact this) hp

theorem polyAt_keepW : Proof.MlDsa.polyAt m' (L.A i o) = Proof.MlDsa.polyAt m (L.A i o) :=
  Proof.MlDsa.Verify.polyAt_frame hf (fun r hr => by have := keepD hL h hw r hr; subst hl; exact this)

end

end

end VG.Proof.MlDsa.Arm.KeyGen

end

end

/-! ### `MlDsa.Arm.KeyGen.StepsCT`, which the modules that import this one used -/

section

/-!
# ML-DSA on 32-bit ARM: two runs in the buffers of a `Site`

Two runs in the same layout, with the same stack pointer (`Two`): a part that
leaks the same, and changes only what `Kept` allows, leaves two runs in it
(`RelCT.two`); and two runs of a part leak the same by taint analysis from
the pointers (`taint7`, `taint4`), or, for the sponge, by `hashS_tr`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Impl.MlKem.Arm (Piece hash copy)
open VG.Spec.Sha3 (rates)

/-- Two runs in the layout `L`, with the same stack pointer. -/
def Two (L : Lay) (Wb : List Nat) (STK : Nat) (x y : State) : Prop :=
  Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp

section
variable {L : Lay} {Wb : List Nat} {STK : Nat}

theorem Two.r7 {x y : State} (h : Two L Wb STK x y) : ∀ r ∈ [Reg.r7], x.gpr r = y.gpr r := fun r hr => by
  rw [List.mem_singleton] at hr; subst hr; rw [h.1.r7, h.2.1.r7]

theorem Two.regs {x y : State} (h : Two L Wb STK x y) : ∀ r ∈ [Reg.r4, .r5, .r6, .r7], x.gpr r = y.gpr r :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h.1.r4, h.2.1.r4]
    · rw [h.1.r5, h.2.1.r5]
    · rw [h.1.r6, h.2.1.r6]
    · rw [h.1.r7, h.2.1.r7]

/-- A part that leaks the same, and keeps the layout, leaves two runs in it. -/
theorem RelCT.two {c : Prog isa} {P : State → State → Prop} (hP : ∀ x y, P x y → Two L Wb STK x y)
    (htr : RelCT isa P c fun _ _ => True)
    (hok : ∀ x, Site L Wb STK x → WP isa c x fun x' => ∃ rs, Kept rs x x') : RelCT isa P c (Two L Wb STK) :=
  (RelCT.wpDep htr (F := fun x x' => ∃ rs, Kept rs x x')
    fun x y h => ⟨hok x (hP x y h).1, hok y (hP x y h).2.1⟩).mono (fun _ _ h => h)
    fun _ _ ⟨_, σ₁, σ₂, hp, ⟨_, hx⟩, ⟨_, hy⟩⟩ => ⟨(hP σ₁ σ₂ hp).1.kept hx, (hP σ₁ σ₂ hp).2.1.kept hy, by
      rw [hx.sp, hy.sp]; exact (hP σ₁ σ₂ hp).2.2⟩

/-- Taint analysis, from the pointer to `scratch`. -/
theorem taint7 {c : Prog isa} {P : State → State → Prop} (hP : ∀ x y, P x y → Two L Wb STK x y)
    {hc : VG.Taint.Hint VG.Arm.taint.T} (h : (VG.Arm.taint.check (Taint.ofRegs [.r7]) c hc).isSome = true) :
    RelCT isa P c fun _ _ => True :=
  taint_prog [.r7] (fun x y hxy => (hP x y hxy).r7) h

/-- Taint analysis, from the pointers of the layout. -/
theorem taint4 {c : Prog isa} {P : State → State → Prop} (hP : ∀ x y, P x y → Two L Wb STK x y)
    {hc : VG.Taint.Hint VG.Arm.taint.T}
    (h : (VG.Arm.taint.check (Taint.ofRegs [.r4, .r5, .r6, .r7]) c hc).isSome = true) :
    RelCT isa P c fun _ _ => True :=
  taint_prog [.r4, .r5, .r6, .r7] (fun x y hxy => (hP x y hxy).regs) h

/-- Two runs of the sponge. -/
theorem hashS_tr {K : Nat → Bool}
    (hK : ∀ i < 5, ∀ j < 5, i ≠ j → 2 ≤ i → 2 ≤ j → K i = true → K j = true → i ∈ Wb ∨ j ∈ Wb)
    {rate sfx : Nat} (hrate : rate ∈ rates) (hre : encodable (BitVec.ofNat 32 rate) = true)
    (hse : encodable (BitVec.ofNat 32 sfx) = true) {ins : List Piece} {q : Piece} (hne : ins ≠ [])
    (hin : ∀ s, Site L Wb STK s → ∀ p ∈ ins, PieceOk (hashLay L s K) ix s false p)
    (hq : ∀ s, Site L Wb STK s → PieceOk (hashLay L s K) ix s true q) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Two L Wb STK x y) : RelCT isa P (hash rate sfx ins [q]) fun _ _ => True :=
  RelCT.mono (RelCT.exists_ fun (s₀ : State) =>
    hash_ct (P := fun a b => s₀ = a ∧ P a b) (L := hashLay L s₀ K) (idx := ix) hrate hre hse hne
      fun a b ⟨e, hab⟩ => by
        subst e
        have ⟨ha, hb, hsp⟩ := hP s₀ b hab
        have hl : hashLay L s₀ K = hashLay L b K := by simp only [hashLay, hsp]
        refine ⟨⟨ha.ctx hK, hin s₀ ha, fun p hp => ?_⟩, ⟨hl ▸ hb.ctx hK, hl ▸ hin b hb, fun p hp => ?_⟩, hsp⟩ <;>
          rw [List.mem_singleton] at hp <;> subst hp
        · exact hq s₀ ha
        · exact hl ▸ hq b hb)
    (fun a b h => ⟨a, rfl, h⟩) fun _ _ h => h

end

end VG.Proof.MlDsa.Arm.KeyGen

end

end

/-!
# ML-DSA on 32-bit ARM: pieces of code, correct and constant time together

As on x86-64: a piece of code takes each run of a function, from an entry
state `σ` that satisfies its precondition `Pre`, from the invariant `I` to `J`
(`ok`), and leaks the same in two runs related by `I` whose entry states agree
on the public data `Pub` (`tr`, `Rel2`). Pieces compose (`Piece.seq`,
`Piece.seqR`), which proves correctness and constant time together.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm
open VG.Impl.MlDsa.Arm.KeyGen (seqR)

/-- Two states each related by `I` to an entry state; the entry states
satisfy `Pre` and agree by `Pub`. -/
def Rel2 (Pre : State → Prop) (Pub : State → State → Prop) (I : State → State → Prop) (s₁ s₂ : State) : Prop :=
  ∃ σ₁ σ₂, Pre σ₁ ∧ Pre σ₂ ∧ Pub σ₁ σ₂ ∧ I σ₁ s₁ ∧ I σ₂ s₂

section
variable {Pre : State → Prop} {Pub : State → State → Prop}

/-- A piece that leaks the same from states related by `I`, and takes each
run from `I` to `I'`. -/
theorem relInv {I I' : State → State → Prop} {c : Prog isa} (hw : ∀ σ s, Pre σ → I σ s → WP isa c s (I' σ))
    (ht : RelCT isa (Rel2 Pre Pub I) c fun _ _ => True) : RelCT isa (Rel2 Pre Pub I) c (Rel2 Pre Pub I') := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  obtain ⟨ht', -⟩ := ht _ _ _ _ _ _ hr e₁ e₂
  obtain ⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩ := hr
  obtain ⟨_, u₁, f₁, g₁⟩ := hw σ₁ s₁ p₁ i₁
  obtain ⟨_, u₂, f₂, g₂⟩ := hw σ₂ s₂ p₂ i₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht', σ₁, σ₂, p₁, p₂, hpub, g₁, g₂⟩

/-- Constant time, from a relation of the runs from the entry states. -/
theorem relStart {c : Prog isa} {Q : State → State → Prop} (h : RelCT isa (Rel2 Pre Pub fun σ s => s = σ) c Q) :
    ConstantTime isa Pre Pub c :=
  RelCT.constantTime (RelCT.mono h (fun s₁ s₂ ⟨p₁, p₂, hp⟩ => ⟨s₁, s₂, p₁, p₂, hp, rfl, rfl⟩) fun _ _ h => h)

/-- `c` takes each run from `I` to `J`, and leaks the same in two runs related by `I`. -/
structure Piece (Pre : State → Prop) (Pub : State → State → Prop) (I J : State → State → Prop) (c : Prog isa) :
    Prop where
  ok : ∀ σ s, Pre σ → I σ s → WP isa c s (J σ)
  tr : RelCT isa (Rel2 Pre Pub I) c fun _ _ => True

variable {I J K : State → State → Prop}

theorem Piece.seq {c₁ c₂ : Prog isa} (h₁ : Piece Pre Pub I J c₁) (h₂ : Piece Pre Pub J K c₂) :
    Piece Pre Pub I K (.seq c₁ c₂) :=
  ⟨fun σ s hp hs => WP.seq (WP.mono (h₁.ok σ s hp hs) fun s' h => h₂.ok σ s' hp h),
    RelCT.seq (relInv h₁.ok h₁.tr) h₂.tr⟩

theorem Piece.mono {c : Prog isa} {I' J' : State → State → Prop} (h : Piece Pre Pub I J c)
    (hI : ∀ σ s, Pre σ → I' σ s → I σ s) (hJ : ∀ σ s, Pre σ → J σ s → J' σ s) : Piece Pre Pub I' J' c :=
  ⟨fun σ s hp hs => WP.mono (h.ok σ s hp (hI σ s hp hs)) fun s' h => hJ σ s' hp h,
    RelCT.mono h.tr (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, i₁, i₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, hI _ _ p₁ i₁, hI _ _ p₂ i₂⟩)
      fun _ _ h => h⟩

theorem Piece.seqR {f : Nat → Prog isa} {I : Nat → State → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → Piece Pre Pub (I k) (I (k + 1)) (f k)) →
      Piece Pre Pub (I a) (I (a + n)) (seqR f a n)
  | 0, a, _ => ⟨fun _ _ _ hs => WP.block_nil hs, fun _ _ _ _ _ _ _ e₁ e₂ => by
      rw [VG.Impl.MlDsa.Arm.KeyGen.seqR, Exec.block_iff] at e₁ e₂
      simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
      obtain ⟨-, rfl⟩ := e₁
      obtain ⟨-, rfl⟩ := e₂
      exact ⟨rfl, trivial⟩⟩
  | n + 1, a, h => by
    have h1 := Piece.seqR (I := I) n (a + 1) fun k h₁ h₂ => h k (by omega_using [h₁]) (by omega_using [h₂])
    rw [show a + (n + 1) = a + 1 + n by omega_using []]
    exact (h a (Nat.le_refl _) (by omega_using [])).seq (c₂ := VG.Impl.MlDsa.Arm.KeyGen.seqR f (a + 1) n) h1

/-- A piece's constant time, from a relation implied by the invariants of two runs. -/
theorem rel_of {c : Prog isa} {Q : State → State → Prop} (htr : RelCT isa Q c fun _ _ => True)
    (h : ∀ σ₁ σ₂ x y, Pre σ₁ → Pre σ₂ → Pub σ₁ σ₂ → I σ₁ x → I σ₂ y → Q x y) :
    RelCT isa (Rel2 Pre Pub I) c fun _ _ => True :=
  RelCT.mono htr (fun _ _ ⟨_, _, p₁, p₂, hpub, i₁, i₂⟩ => h _ _ _ _ p₁ p₂ hpub i₁ i₂) fun _ _ h => h

end

end VG.Proof.MlDsa.Arm.KeyGen

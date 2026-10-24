module

public import VerifiedGarbage.Proof.MlKem.PPC64LE.Prf
import VerifiedGarbage.Proof.MlKem.PPC64LE.Loops
import VerifiedGarbage.Proof.MlKem.PPC64LE.HashTop
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on PPC64LE: a row of `Â ∘ v̂`

As on 32-bit ARM (`Proof/MlKem/Arm/RowSum.lean`). `K.rowSum transpose` sums,
in polynomial `3k + 2`, the products of the entries `j < k` (in `r25`) of row
`i` (in `r26`) of `Â` (or of `Â^⊺`, `transpose`) with polynomials `k + j`,
sampling each entry into polynomial `3k + 4` from the seed `ρ ‖ j ‖ i`
(`ρ ‖ i ‖ j`) at 1248. If a `SampleNTT` does not finish, the product uses
polynomial `k + j` in its place (`effA`), and the flag in `r24` becomes 0
(`rowSum_ok`). The sum is `KPke.dotK` (`rowAcc_eq`). `K.dot` sums the
products of polynomials `j` and `k + j` (`dot_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.PPC64LE

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-! ## The algorithm -/

/-- The seed of entry `j` of row `i`: that of `Â[i, j]`, or of `Â[j, i]`. -/
def rowSeed (transpose : Bool) (ρ : List Byte) (i j : Nat) : List Byte :=
  if transpose then VG.Proof.MlKem.matSeed ρ j i else VG.Proof.MlKem.matSeed ρ i j

/-- The entry the product uses: the sampled one, or `v` if `SampleNTT` does not finish. -/
def effA (transpose : Bool) (ρ : List Byte) (i j : Nat) (v : Poly) : Poly :=
  (sampleNTT 280 (rowSeed transpose ρ i j)).getD v

/-- The sum of the first `j` products. -/
def rowAcc (a v : Nat → Poly) : Nat → Poly
  | 0 => zero
  | j + 1 => add (rowAcc a v j) (multiplyNTTs (a j) (v j))

/-- Whether the first `j` entries' `SampleNTT`s finished. -/
def okRow (transpose : Bool) (ρ : List Byte) (i j : Nat) : Bool :=
  (List.range j).all fun j' => (sampleNTT 280 (rowSeed transpose ρ i j')).isSome

theorem okRow_succ (transpose : Bool) (ρ : List Byte) (i j : Nat) :
    okRow transpose ρ i (j + 1) = (okRow transpose ρ i j && (sampleNTT 280 (rowSeed transpose ρ i j)).isSome) := by
  simp only [okRow, List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true]

theorem rowAcc_eq (a v : Nat → Poly) : ∀ k, rowAcc a v k = VG.Proof.MlKem.KPke.dotK a v k
  | 0 => rfl
  | k + 1 => by
    rw [rowAcc, rowAcc_eq a v k]
    exact (VG.Proof.MlKem.KPke.foldK_succ VG.Proof.MlKem.zero_add_poly _ k).symm

/-! ## The blocks -/

section
variable {K : KemLay} (hK : K.WF)
include hK

theorem oAcc_lt : K.oAcc < 32768 := by offs
theorem oTmp_lt : K.oTmp < 32768 := by offs
theorem oAhat_lt : K.oAhat < 32768 := by offs
theorem oSample_lt : K.oSample < 32768 := by offs
theorem oNtt_lt : K.oNtt < 32768 := by offs
theorem oPolyK_lt : oPoly K.k < 32768 := by offs

end

section
variable {K : KemLay} {s : State} {P : BitVec 64} {i j : Nat}

theorem seedArgs_ok (hK : K.WF) (transpose : Bool) (h31 : s.gpr .r31 = P) (h26 : s.gpr .r26 = BitVec.ofNat 64 i)
    (h25 : s.gpr .r25 = BitVec.ofNat 64 j) (hi : i < 256) (hj : j < 256)
    (w1 : InRegions s.wr (P + BitVec.ofNat 64 (oSeed + 32)) 1)
    (w2 : InRegions s.wr (P + BitVec.ofNat 64 (oSeed + 33)) 1) :
    WP isa (.block (seedBytes transpose ++ [.addi .r3 .r31 oSeed, .addi .r4 .r31 K.oAhat, .addi .r5 .r31 K.oSample]))
      s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
        s'.mem = (s.mem.writeW (P + BitVec.ofNat 64 (oSeed + 32)) (BitVec.ofNat 8 (if transpose then i else j))).writeW
          (P + BitVec.ofNat 64 (oSeed + 33)) (BitVec.ofNat 8 (if transpose then j else i)) ∧
        s'.gpr .r3 = P + BitVec.ofNat 64 oSeed ∧ s'.gpr .r4 = P + BitVec.ofNat 64 K.oAhat ∧
        s'.gpr .r5 = P + BitVec.ofNat 64 K.oSample := by
  have e1 : oSeed < 32768 := by decide
  have e2 : K.oAhat < 32768 := oAhat_lt hK
  have e3 : K.oSample < 32768 := oSample_lt hK
  have o1 : oSeed + 32 < 2 ^ 15 := by decide
  have o2 : oSeed + 33 < 2 ^ 15 := by decide
  have si := setWidth8_ofNat (N := i) (by omega)
  have sj := setWidth8_ofNat (N := j) (by omega)
  cases transpose <;>
  · prun [seedBytes, exec_stb, List.cons_append, List.nil_append, Bool.false_eq_true, ite_true, ite_false, e1, e2, e3,
      o1, o2, h31, h25, h26, w1, w2, si, sj]
    and_intros <;> first | exact trivial | rfl | pres_tac

theorem flag_ok {b c : Bool} (h3 : s.gpr .r3 = if c then 1 else 0) (h24 : s.gpr .r24 = if b then 1 else 0) :
    WP isa (.block [.logic .and .r24 .r24 .r3]) s fun s' =>
      KeptX [.r24] [] s s' ∧ s'.gpr .r24 = (if b && c then 1 else 0) ∧ s'.gpr .r3 = s.gpr .r3 ∧ s'.mem = s.mem := by
  prun [h3, h24]
  refine ⟨⟨fun r _ hx => ?_, rfl, rfl, rfl, Frame.refl _ _⟩, ?_, trivial⟩
  · exact RegUpd.gpr_write_of_ne _ _ fun e => hx (by rw [e]; exact List.mem_singleton_self _)
  · cases b <;> cases c <;> rfl

theorem selT_ok (hK : K.WF) (h31 : s.gpr .r31 = P) (h25 : s.gpr .r25 = BitVec.ofNat 64 j) :
    WP isa (.block (slotAt .r4 .r25 (oPoly K.k))) s fun s' =>
      Only s s' ∧ s'.gpr .r4 = P + BitVec.ofNat 64 j <<< 10 + BitVec.ofNat 64 (oPoly K.k) := by
  have e1 : oPoly K.k < 32768 := oPolyK_lt hK
  prun [slotAt, e1, h31, h25]
  exact ⟨Only.of_writes rfl rfl rfl rfl (by pres_tac), trivial⟩

theorem selF_ok (hK : K.WF) (h31 : s.gpr .r31 = P) :
    WP isa (.block [.addi .r4 .r31 K.oAhat]) s fun s' => Only s s' ∧ s'.gpr .r4 = P + BitVec.ofNat 64 K.oAhat := by
  have e1 : K.oAhat < 32768 := oAhat_lt hK
  prun [e1, h31]
  exact ⟨Only.of_writes rfl rfl rfl rfl (by pres_tac), trivial⟩

theorem mulArgs_ok (hK : K.WF) (h31 : s.gpr .r31 = P) (h25 : s.gpr .r25 = BitVec.ofNat 64 j) :
    WP isa (.block (.addi .r3 .r31 K.oTmp :: slotAt .r5 .r25 (oPoly K.k) ++ [.addi .r6 .r31 K.oNtt])) s fun s' =>
      Only s s' ∧ s'.gpr .r3 = P + BitVec.ofNat 64 K.oTmp ∧ s'.gpr .r4 = s.gpr .r4 ∧
      s'.gpr .r5 = P + BitVec.ofNat 64 j <<< 10 + BitVec.ofNat 64 (oPoly K.k) ∧
      s'.gpr .r6 = P + BitVec.ofNat 64 K.oNtt := by
  have e1 : K.oTmp < 32768 := oTmp_lt hK
  have e2 : oPoly K.k < 32768 := oPolyK_lt hK
  have e3 : K.oNtt < 32768 := oNtt_lt hK
  prun [slotAt, List.cons_append, List.nil_append, e1, e2, e3, h31, h25]
  exact ⟨Only.of_writes rfl rfl rfl rfl (by pres_tac), trivial⟩

theorem accArgs_ok {o o' : Nat} (h31 : s.gpr .r31 = P) (he : o < 32768) (he' : o' < 32768) :
    WP isa (.block [.addi .r3 .r31 o, .addi .r4 .r31 o']) s fun s' =>
      Only s s' ∧ s'.gpr .r3 = P + BitVec.ofNat 64 o ∧ s'.gpr .r4 = P + BitVec.ofNat 64 o' := by
  prun [he, he', h31]
  exact ⟨Only.of_writes rfl rfl rfl rfl (by pres_tac), trivial⟩

end

/-! ## The loop -/

/-- What a row needs of the state it starts from. -/
structure RowPre (K : KemLay) (L : Lay) (ρ : List Byte) (v : Nat → Poly) (i : Nat) (fl : Bool) (s : State) : Prop where
  wf : K.WF
  ctx : Ctx L s
  ik : i < K.k
  r26 : s.gpr .r26 = BitVec.ofNat 64 i
  r24 : s.gpr .r24 = if fl then 1 else 0
  rho : bytesAt s.mem (L.A 0 oSeed) 32 = ρ
  vec : ∀ j < K.k, PolyIs s.mem (L.A 0 (oPoly (K.k + j))) (v j)

/-- What a row changes: the indices of the seed, polynomials `3k + 2` to
`3k + 4`, the working space of the callees and the stack. -/
abbrev rowW (K : KemLay) : List (Nat × Nat × Nat) :=
  [(0, 1280, 2), (0, K.oAcc, 3072), (0, K.oSample, 3072), (1, 0, 48)]

/-- After the first `j` entries of the row. -/
structure RowInv (K : KemLay) (L : Lay) (transpose : Bool) (ρ : List Byte) (v : Nat → Poly) (i : Nat) (fl : Bool)
    (s₀ : State) (j : Nat) (s : State) : Prop where
  kx : KeptX [.r25, .r24] (L.RL (rowW K)) s₀ s
  r25 : s.gpr .r25 = BitVec.ofNat 64 j
  r24 : s.gpr .r24 = if fl && okRow transpose ρ i j then 1 else 0
  acc : PolyIs s.mem (L.A 0 K.oAcc) (rowAcc (fun j => effA transpose ρ i j (v j)) v j)

/-- The polynomials of `v̂` apart from what a row changes. -/
abbrev RowWVec (K : KemLay) : Prop := ∀ j < K.k, (rowW K).all (sep0 (oPoly (K.k + j)) 1024) = true

/-- The facts on the offsets of `scratch` that a row's steps use. -/
abbrev RowLF (K : KemLay) : Prop :=
  (rowW K).all (sep0 oSeed 32) = true ∧ [((0 : Nat), (1280 : Nat), (2 : Nat))].all (fun w => (rowW K).any (subB0 w)) = true ∧
  K.oAcc + 1024 ≤ 32768 ∧ [((0 : Nat), (1280 : Nat), (2 : Nat))].all (sep0 K.oAcc 1024) = true ∧
  K.oAhat + 1024 ≤ 32768 ∧ (oSeed + 34 ≤ K.oAhat ∨ K.oAhat + 1024 ≤ oSeed) ∧
  K.oSample + 2048 ≤ 32768 ∧ (oSeed + 34 ≤ K.oSample ∨ K.oSample + 2048 ≤ oSeed) ∧
  (K.oAhat + 1024 ≤ K.oSample ∨ K.oSample + 2048 ≤ K.oAhat) ∧
  [((0 : Nat), K.oAhat, (1024 : Nat)), (0, K.oSample, 2048), (1, 0, 48)].all (fun w => (rowW K).any (subB0 w)) = true ∧
  [((0 : Nat), K.oAhat, (1024 : Nat)), (0, K.oSample, 2048), (1, 0, 48)].all (sep0 K.oAcc 1024) = true ∧
  [((0 : Nat), K.oTmp, (1024 : Nat)), (0, K.oNtt, 1024)].all (fun w => (rowW K).any (subB0 w)) = true ∧
  [((0 : Nat), K.oTmp, (1024 : Nat)), (0, K.oNtt, 1024)].all (sep0 K.oAcc 1024) = true ∧
  K.oTmp + 1024 ≤ 32768 ∧ (K.oAcc + 1024 ≤ K.oTmp ∨ K.oTmp + 1024 ≤ K.oAcc) ∧
  [((0 : Nat), K.oAcc, (1024 : Nat))].all (fun w => (rowW K).any (subB0 w)) = true

theorem row_lf {K : KemLay} (hK : K.WF) : RowLF K :=
  (by decide : ∀ k < 5, RowLF (kOf k)) K.k (by have := hK.k4; omega)

theorem rowW_vec {K : KemLay} (hK : K.WF) : RowWVec K :=
  (by decide : ∀ k < 5, RowWVec (kOf k)) K.k (by have := hK.k4; omega)

theorem bytes_two (m : Mem) (p : Addr) : bytesAt m p 2 = [m p, m (p + BitVec.ofNat 64 1)] := by
  simp only [bytesAt, show List.range 2 = [0, 1] from rfl, List.map_cons, List.map_nil,
    BitVec.add_zero]

theorem rowSeed_eq (transpose : Bool) (ρ : List Byte) (i j : Nat) :
    rowSeed transpose ρ i j =
      ρ ++ [BitVec.ofNat 8 (if transpose then i else j), BitVec.ofNat 8 (if transpose then j else i)] := by
  cases transpose <;> rfl

/-! ### The steps of an iteration -/

/-- Whether entry `j`'s `SampleNTT` finishes. -/
abbrev cOk (transpose : Bool) (ρ : List Byte) (i j : Nat) : Bool := (sampleNTT 280 (rowSeed transpose ρ i j)).isSome

/-- Where the product takes the entry from. -/
abbrev oSel (K : KemLay) (c : Bool) (j : Nat) : Nat := if c then K.oAhat else oPoly (K.k + j)

section
variable (K : KemLay) (L : Lay) (transpose : Bool) (ρ : List Byte) (v : Nat → Poly) (i : Nat) (fl : Bool)
  (s₀ : State) (j : Nat)

/-- What holds through an iteration: what it changed, the counter, the sum so far. -/
structure RS (s : State) : Prop where
  kx : KeptX [.r25, .r24] (L.RL (rowW K)) s₀ s
  r25 : s.gpr .r25 = BitVec.ofNat 64 j
  acc : PolyIs s.mem (L.A 0 K.oAcc) (rowAcc (fun j => effA transpose ρ i j (v j)) v j)

/-- After the seed and the arguments of `SampleNTT`. -/
structure RA (s : State) : Prop where
  rs : RS K L transpose ρ v i s₀ j s
  r24 : s.gpr .r24 = if fl && okRow transpose ρ i j then 1 else 0
  r3 : s.gpr .r3 = L.A 0 oSeed
  r4 : s.gpr .r4 = L.A 0 K.oAhat
  r5 : s.gpr .r5 = L.A 0 K.oSample
  seed : bytesAt s.mem (L.A 0 oSeed) 34 = rowSeed transpose ρ i j

/-- After `SampleNTT`. -/
structure RB (s : State) : Prop where
  rs : RS K L transpose ρ v i s₀ j s
  r24 : s.gpr .r24 = if fl && okRow transpose ρ i j then 1 else 0
  r3 : s.gpr .r3 = if cOk transpose ρ i j then 1 else 0
  ahat : ∀ a, sampleNTT 280 (rowSeed transpose ρ i j) = some a → PolyIs s.mem (L.A 0 K.oAhat) a

/-- After the flag. -/
structure RC (s : State) : Prop where
  rs : RS K L transpose ρ v i s₀ j s
  r24 : s.gpr .r24 = if fl && okRow transpose ρ i (j + 1) then 1 else 0
  r3 : s.gpr .r3 = if cOk transpose ρ i j then 1 else 0
  ahat : ∀ a, sampleNTT 280 (rowSeed transpose ρ i j) = some a → PolyIs s.mem (L.A 0 K.oAhat) a

/-- After the selection of the entry. -/
structure RD (s : State) : Prop where
  rs : RS K L transpose ρ v i s₀ j s
  r24 : s.gpr .r24 = if fl && okRow transpose ρ i (j + 1) then 1 else 0
  r4 : s.gpr .r4 = L.A 0 (oSel K (cOk transpose ρ i j) j)
  sel : PolyIs s.mem (L.A 0 (oSel K (cOk transpose ρ i j) j)) (effA transpose ρ i j (v j))

/-- After the arguments of the product. -/
structure RE (s : State) : Prop where
  rd : RD K L transpose ρ v i fl s₀ j s
  r3 : s.gpr .r3 = L.A 0 K.oTmp
  r5 : s.gpr .r5 = L.A 0 (oPoly (K.k + j))
  r6 : s.gpr .r6 = L.A 0 K.oNtt

/-- After the product. -/
structure RF (s : State) : Prop where
  rs : RS K L transpose ρ v i s₀ j s
  r24 : s.gpr .r24 = if fl && okRow transpose ρ i (j + 1) then 1 else 0
  tmp : PolyIs s.mem (L.A 0 K.oTmp) (multiplyNTTs (effA transpose ρ i j (v j)) (v j))

/-- After the arguments of the sum. -/
structure RG (s : State) : Prop where
  rf : RF K L transpose ρ v i fl s₀ j s
  r3 : s.gpr .r3 = L.A 0 K.oAcc
  r4 : s.gpr .r4 = L.A 0 K.oTmp

/-- After the sum. -/
structure RH (s : State) : Prop where
  kx : KeptX [.r25, .r24] (L.RL (rowW K)) s₀ s
  r25 : s.gpr .r25 = BitVec.ofNat 64 j
  r24 : s.gpr .r24 = if fl && okRow transpose ρ i (j + 1) then 1 else 0
  acc : PolyIs s.mem (L.A 0 K.oAcc) (rowAcc (fun j => effA transpose ρ i j (v j)) v (j + 1))

end

section
variable {K : KemLay} {L : Lay} {transpose : Bool} {ρ : List Byte} {v : Nat → Poly} {i : Nat} {fl : Bool}
  {s₀ : State} {j : Nat}

theorem RS.ctx (hp : RowPre K L ρ v i fl s₀) {s : State} (h : RS K L transpose ρ v i s₀ j s) : Ctx L s :=
  h.kx.ctx (by decide) hp.ctx

theorem RS.r26 (hp : RowPre K L ρ v i fl s₀) {s : State} (h : RS K L transpose ρ v i s₀ j s) :
    s.gpr .r26 = BitVec.ofNat 64 i := by
  rw [h.kx.cs .r26 (by decide) (by decide), hp.r26]

theorem RS.vec (hp : RowPre K L ρ v i fl s₀) (hj : j < K.k) {s : State} (h : RS K L transpose ρ v i s₀ j s) :
    PolyIs s.mem (L.A 0 (oPoly (K.k + j))) (v j) := by
  have hK := hp.wf
  exact Lay.polyIs_keep hp.ctx.ok h.kx.frame (hp.ctx.sepAll0 (by offs) (rowW_vec hp.wf j hj)) (hp.vec j hj)

/-- A step that keeps `RS`: it changes only the regions of `rowW K` and not `r25`, nor the sum. -/
theorem RS.step (hp : RowPre K L ρ v i fl s₀) {s s' : State} (h : RS K L transpose ρ v i s₀ j s) {xs : List Reg}
    {W : List (Nat × Nat × Nat)} (hk : KeptX xs (L.RL W) s s') (hx : ∀ x ∈ xs, x ∈ [Reg.r25, .r24])
    (h25 : Reg.r25 ∉ xs) (hW : W.all (fun w => (rowW K).any (subB0 w)) = true)
    (hA : sepAll L.sizes (0, K.oAcc, 1024) W = true) : RS K L transpose ρ v i s₀ j s' :=
  ⟨h.kx.trans ((hk.weaken hx).subL hp.ctx hW), by rw [hk.cs .r25 (by decide) h25, h.r25],
    Lay.polyIs_keep hp.ctx.ok hk.frame hA h.acc⟩

theorem rowA_ok (hp : RowPre K L ρ v i fl s₀) (hj : j < K.k) {s : State}
    (h : RowInv K L transpose ρ v i fl s₀ j s) :
    WP isa (.block (seedBytes transpose ++ [.addi .r3 .r31 oSeed, .addi .r4 .r31 K.oAhat, .addi .r5 .r31 K.oSample]))
      s (RA K L transpose ρ v i fl s₀ j) := by
  have hK := hp.wf
  have k4 := hK.k4
  have hL := hp.ctx.ok
  have hi := hp.ik
  have hc := h.kx.ctx (by decide) hp.ctx
  have g26 : s.gpr .r26 = BitVec.ofNat 64 i := by rw [h.kx.cs .r26 (by decide) (by decide), hp.r26]
  have ρs : bytesAt s.mem (L.A 0 oSeed) 32 = ρ := by
    rw [← hp.rho]; exact Lay.bytes_keep hL h.kx.frame (hp.ctx.sepAll0 (by decide) (row_lf hK).1) (by decide)
  have w1 : InRegions s.wr (L.ptr 0 + BitVec.ofNat 64 (oSeed + 32)) 1 :=
    hc.cs (o := 1280) (l := 1) (by decide) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  have w2 : InRegions s.wr (L.ptr 0 + BitVec.ofNat 64 (oSeed + 33)) 1 :=
    hc.cs (o := 1281) (l := 1) (by decide) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  refine WP.mono (seedArgs_ok hK transpose hc.r31 g26 h.r25 (by omega) (by omega) w1 w2)
    fun s₁ ⟨cs₁, rd₁, wr₁, sp₁, m₁, g3, g4, g5⟩ => ?_
  have m₁' : s₁.mem = (s.mem.writeW (L.A 0 1280) (BitVec.ofNat 8 (if transpose then i else j))).writeW (L.A 0 1281)
      (BitVec.ofNat 8 (if transpose then j else i)) := m₁
  have k₁ : KeptX [] (L.RL [(0, 1280, 2)]) s s₁ := by
    refine ⟨fun r hr _ => cs₁ r hr, sp₁, rd₁, wr₁, ?_⟩
    rw [m₁']
    have c1 : (L.R 0 1280 2).Contains (L.A 0 1280) 1 := Offset.contains _ (by omega) (by omega) (by omega)
    have c2 : (L.R 0 1280 2).Contains (L.A 0 1281) 1 := Offset.contains _ (by omega) (by omega) (by omega)
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c1).writeW (List.mem_singleton_self _) _ c2
  have ne : (L.A 0 1280 : Addr) ≠ L.A 0 1281 := Offset.add_ofNat_ne _ (by omega) (by omega) (by omega)
  have b1 : s₁.mem (L.A 0 1280) = BitVec.ofNat 8 (if transpose then i else j) := by
    rw [m₁', writeW8_apply, writeW8_apply, ite_eq_right ne, ite_eq_left rfl]
  have b2 : s₁.mem (L.A 0 1281) = BitVec.ofNat 8 (if transpose then j else i) := by
    rw [m₁', writeW8_apply, ite_eq_left rfl]
  refine ⟨⟨h.kx.trans ((k₁.weaken (by simp)).subL hp.ctx (row_lf hK).2.1),
    by rw [k₁.cs .r25 (by decide) (by decide), h.r25],
    Lay.polyIs_keep hL k₁.frame (hc.sepAll0 (row_lf hK).2.2.1 (row_lf hK).2.2.2.1) h.acc⟩,
    by rw [k₁.cs .r24 (by decide) (by decide), h.r24], g3, g4, g5, ?_⟩
  rw [rowSeed_eq]
  show bytesAt s₁.mem (L.ptr 0 + BitVec.ofNat 64 1248) (32 + 2) = _
  rw [bytesAt_add, bytes_two, ptr_add, ptr_add]
  congr 1
  · rw [← ρs]
    exact Lay.bytes_keep hL k₁.frame (hc.sepAll0 (by decide) (by decide)) (by decide)
  · rw [b1, b2]

theorem rowB_ok (hp : RowPre K L ρ v i fl s₀) {s : State} (h : RA K L transpose ρ v i fl s₀ j s) :
    WP isa callSample s (RB K L transpose ρ v i fl s₀ j) := by
  have hK := hp.wf
  have hc := h.rs.ctx hp
  have lf := row_lf hK
  refine sampleL hc h.r3 h.r4 h.r5 (hc.sep00 (by decide) lf.2.2.2.2.1 lf.2.2.2.2.2.1)
    (hc.sep00 (by decide) lf.2.2.2.2.2.2.1 lf.2.2.2.2.2.2.2.1)
    (hc.sep00 lf.2.2.2.2.1 lf.2.2.2.2.2.2.1 lf.2.2.2.2.2.2.2.2.1)
    (hc.sep01 (by decide) (by decide)) (hc.sep01 lf.2.2.2.2.1 (by decide)) (hc.sep01 lf.2.2.2.2.2.2.1 (by decide))
    (mem_rd_wr hc.cw) hc.cw hc.cw fun s' k' r3' a' => ?_
  rw [h.seed] at r3' a'
  exact ⟨h.rs.step hp (k'.x []) (by simp) (by simp) lf.2.2.2.2.2.2.2.2.2.1
      (hc.sepAll0 lf.2.2.1 lf.2.2.2.2.2.2.2.2.2.2.1),
    by rw [k'.cs .r24 (by decide), h.r24], r3', a'⟩

theorem rowC_ok {s : State} (hp : RowPre K L ρ v i fl s₀) (h : RB K L transpose ρ v i fl s₀ j s) :
    WP isa (.block [.logic .and .r24 .r24 .r3]) s (RC K L transpose ρ v i fl s₀ j) :=
  WP.mono (flag_ok h.r3 h.r24) fun s' ⟨k', f', g3', m'⟩ =>
    ⟨h.rs.step hp (W := []) k' (by simp) (by decide) rfl rfl,
      by rw [f', Bool.and_assoc, ← okRow_succ], by rw [g3', h.r3], by rw [m']; exact h.ahat⟩

theorem rowD_ok (hp : RowPre K L ρ v i fl s₀) (hj : j < K.k) {s : State} (h : RC K L transpose ρ v i fl s₀ j s) :
    WP isa (.ite (.zero .d .r3) (.block (slotAt .r4 .r25 (oPoly K.k))) (.block [.addi .r4 .r31 K.oAhat])) s
      (RD K L transpose ρ v i fl s₀ j) := by
  have hK := hp.wf
  have hc := h.rs.ctx hp
  have eo : oPoly (K.k + j) = oPoly K.k + 1024 * j := by simp only [oPoly]; omega
  refine WP.ite (s.gpr .r3 == 0) (eval_zero _ _) (fun hz => WP.mono (selT_ok hK hc.r31 h.rs.r25)
    fun s₄ ⟨o₄, g4₄⟩ => ?_) (fun hz => WP.mono (selF_ok hK hc.r31) fun s₄ ⟨o₄, g4₄⟩ => ?_)
  · have hc' : cOk transpose ρ i j = false := by
      rw [h.r3] at hz; cases e : cOk transpose ρ i j <;> simp_all
    rw [slot_eq _ (by offs), ← eo] at g4₄
    have e : effA transpose ρ i j (v j) = v j := by
      simp only [effA]
      simp only [cOk] at hc'
      cases e' : sampleNTT 280 (rowSeed transpose ρ i j)
      · rfl
      · rw [e'] at hc'; cases hc'
    refine ⟨h.rs.step hp (o₄.x [] []) (W := []) (by simp) (by simp) rfl rfl,
      by rw [o₄.cs .r24 (by decide), h.r24], by rw [g4₄, hc']; rfl, ?_⟩
    rw [hc', e, o₄.mem]; exact h.rs.vec hp hj
  · have hc' : cOk transpose ρ i j = true := by
      rw [h.r3] at hz; cases e : cOk transpose ρ i j <;> simp_all
    refine ⟨h.rs.step hp (o₄.x [] []) (W := []) (by simp) (by simp) rfl rfl,
      by rw [o₄.cs .r24 (by decide), h.r24], by rw [g4₄, hc']; rfl, ?_⟩
    simp only [cOk] at hc'
    cases e' : sampleNTT 280 (rowSeed transpose ρ i j) with
    | none => rw [e'] at hc'; cases hc'
    | some a =>
      have e : effA transpose ρ i j (v j) = a := by simp only [effA, e', Option.getD_some]
      rw [e, o₄.mem, show oSel K (cOk transpose ρ i j) j = K.oAhat by simp [cOk, e']]
      exact h.ahat a e'

theorem rowE_ok (hp : RowPre K L ρ v i fl s₀) (hj : j < K.k) {s : State} (h : RD K L transpose ρ v i fl s₀ j s) :
    WP isa (.block (.addi .r3 .r31 K.oTmp :: slotAt .r5 .r25 (oPoly K.k) ++ [.addi .r6 .r31 K.oNtt])) s
      (RE K L transpose ρ v i fl s₀ j) := by
  have hK := hp.wf
  have hc := h.rs.ctx hp
  have eo : oPoly (K.k + j) = oPoly K.k + 1024 * j := by simp only [oPoly]; omega
  refine WP.mono (mulArgs_ok (j := j) hK hc.r31 h.rs.r25) fun s' ⟨o', m3, m4, m5, m6⟩ => ?_
  rw [slot_eq _ (by offs), ← eo] at m5
  exact ⟨⟨h.rs.step hp (o'.x [] []) (W := []) (by simp) (by simp) rfl rfl,
    by rw [o'.cs .r24 (by decide), h.r24], by rw [m4, h.r4], by rw [o'.mem]; exact h.sel⟩, m3, m5, m6⟩

theorem sel_sep (hK : K.WF) (c : Bool) {j : Nat} (hj : j < K.k) :
    oSel K c j + 1024 ≤ 32768 ∧ (K.oTmp + 1024 ≤ oSel K c j ∨ oSel K c j + 1024 ≤ K.oTmp) ∧
      (oSel K c j + 1024 ≤ K.oNtt ∨ K.oNtt + 1024 ≤ oSel K c j) := by
  cases c <;> simp only [oSel, Bool.false_eq_true, ite_false, ite_true] <;> offs

theorem rowF_ok (hp : RowPre K L ρ v i fl s₀) (hj : j < K.k) {s : State} (h : RE K L transpose ρ v i fl s₀ j s) :
    WP isa callMul s (RF K L transpose ρ v i fl s₀ j) := by
  have hK := hp.wf
  have hc := h.rd.rs.ctx hp
  have lf := row_lf hK
  obtain ⟨s1, s2, s3⟩ := sel_sep hK (cOk transpose ρ i j) hj
  refine mulL hc.ok h.r3 h.rd.r4 h.r5 h.r6 (hc.sep00 (by offs) s1 s2) (hc.sep00 (by offs) (by offs) (by offs))
    (hc.sep00 (by offs) (by offs) (by offs)) (hc.sep00 s1 (by offs) s3) (hc.sep00 (by offs) (by offs) (by offs))
    hc.cw (mem_rd_wr hc.cw) (mem_rd_wr hc.cw) hc.cw h.rd.sel (h.rd.rs.vec hp hj) fun s' k' p' => ?_
  exact ⟨h.rd.rs.step hp (k'.x []) (by simp) (by simp) lf.2.2.2.2.2.2.2.2.2.2.2.1
      (hc.sepAll0 lf.2.2.1 lf.2.2.2.2.2.2.2.2.2.2.2.2.1),
    by rw [k'.cs .r24 (by decide), h.rd.r24], p'⟩

theorem rowG_ok (hp : RowPre K L ρ v i fl s₀) {s : State} (h : RF K L transpose ρ v i fl s₀ j s) :
    WP isa (.block [.addi .r3 .r31 K.oAcc, .addi .r4 .r31 K.oTmp]) s (RG K L transpose ρ v i fl s₀ j) := by
  have hK := hp.wf
  have hc := h.rs.ctx hp
  exact WP.mono (accArgs_ok hc.r31 (oAcc_lt hK) (oTmp_lt hK)) fun s' ⟨o', a3, a4⟩ =>
    ⟨⟨h.rs.step hp (o'.x [] []) (W := []) (by simp) (by simp) rfl rfl,
      by rw [o'.cs .r24 (by decide), h.r24], by rw [o'.mem]; exact h.tmp⟩, a3, a4⟩

theorem rowH_ok (hp : RowPre K L ρ v i fl s₀) {s : State} (h : RG K L transpose ρ v i fl s₀ j s) :
    WP isa callAdd s (RH K L transpose ρ v i fl s₀ j) := by
  have hK := hp.wf
  have hc := h.rf.rs.ctx hp
  have lf := row_lf hK
  refine addL hc.ok h.r3 h.r4 (hc.sep00 lf.2.2.1 lf.2.2.2.2.2.2.2.2.2.2.2.2.2.1 lf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    hc.cw (mem_rd_wr hc.cw) h.rf.rs.acc h.rf.tmp fun s' k' p' => ?_
  exact ⟨h.rf.rs.kx.trans ((k'.x _).subL hp.ctx lf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2),
    by rw [k'.cs .r25 (by decide), h.rf.rs.r25], by rw [k'.cs .r24 (by decide), h.rf.r24], p'⟩

theorem rowI_ok (hK : K.WF) {s : State} (hj : j < K.k) (h : RH K L transpose ρ v i fl s₀ j s) :
    WP isa (.block (count .r25 K.k)) s fun s' =>
      RowInv K L transpose ρ v i fl s₀ (j + 1) s' ∧ (s'.gpr .r0 != 0) = decide (j + 1 ≠ K.k) := by
  have k4 := hK.k4
  exact WP.mono (count_ok (by decide) (by omega) (by omega) h.r25) fun s' ⟨k', g', z'⟩ =>
    ⟨⟨h.kx.trans ((k'.weaken (by simp)).mono (fun _ h => absurd h List.not_mem_nil)), g',
      by rw [k'.cs .r24 (by decide) (by decide), h.r24],
      polyIs_frame k'.frame (fun _ h => absurd h List.not_mem_nil) h.acc⟩, z'⟩

theorem rowBody_ok (hp : RowPre K L ρ v i fl s₀) (hj : j < K.k) {s : State}
    (h : RowInv K L transpose ρ v i fl s₀ j s) :
    WP isa (K.rowBody transpose) s fun s' =>
      RowInv K L transpose ρ v i fl s₀ (j + 1) s' ∧ (s'.gpr .r0 != 0) = decide (j + 1 ≠ K.k) :=
  WP.seq (WP.mono (rowA_ok hp hj h) fun _ h₁ => WP.seq (WP.mono (rowB_ok hp h₁) fun _ h₂ =>
    WP.seq (WP.mono (rowC_ok hp h₂) fun _ h₃ => WP.seq (WP.mono (rowD_ok hp hj h₃) fun _ h₄ =>
    WP.seq (WP.mono (rowE_ok hp hj h₄) fun _ h₅ => WP.seq (WP.mono (rowF_ok hp hj h₅) fun _ h₆ =>
    WP.seq (WP.mono (rowG_ok hp h₆) fun _ h₇ => WP.seq (WP.mono (rowH_ok hp h₇) fun _ h₈ =>
      rowI_ok hp.wf hj h₈))))))))

end

theorem li_ok {s : State} (c : Reg) {N : Nat} (he : N < 32768) :
    WP isa (.block [.li c N]) s fun s' =>
      KeptX [c] [] s s' ∧ s'.gpr c = BitVec.ofNat 64 N ∧ s'.mem = s.mem := by
  prun [he]
  refine ⟨⟨fun r _ hx => ?_, rfl, rfl, rfl, Frame.refl _ _⟩, trivial⟩
  exact RegUpd.gpr_write_of_ne _ _ fun e => hx (by rw [e]; exact List.mem_singleton_self _)

theorem rowSum_ok {K : KemLay} {L : Lay} {transpose : Bool} {ρ : List Byte} {v : Nat → Poly} {i : Nat}
    {fl : Bool} {s₀ : State} (hp : RowPre K L ρ v i fl s₀) :
    WP isa (K.rowSum transpose) s₀ (RowInv K L transpose ρ v i fl s₀ K.k) := by
  have hK := hp.wf
  have lf := row_lf hK
  refine WP.seq (WP.mono (zeroPoly_ok hp.ctx lf.2.2.1) fun s₁ ⟨k₁, z₁⟩ => ?_)
  refine WP.seq (WP.mono (li_ok .r25 (N := 0) (by decide)) fun s₂ ⟨k₂, g₂, m₂⟩ => ?_)
  refine wp_loop_nz (RowInv K L transpose ρ v i fl s₀) (N := K.k) (by have := hK.k1; omega)
    (fun j hj s h => rowBody_ok hp hj h) (fun _ h => h) ⟨?_, g₂, ?_, by rw [m₂]; exact z₁⟩
  · exact ((k₁.x _).subL hp.ctx lf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2).trans
      ((k₂.weaken (by simp)).mono (fun _ h => absurd h List.not_mem_nil))
  · rw [k₂.cs .r24 (by decide) (by decide), k₁.cs .r24 (by decide), hp.r24]
    simp [okRow]

/-! ## `dot` -/

theorem dotArgs_ok {K : KemLay} (hK : K.WF) {s : State} {P : BitVec 64} {j : Nat} (h31 : s.gpr .r31 = P)
    (h25 : s.gpr .r25 = BitVec.ofNat 64 j) :
    WP isa (.block (.addi .r3 .r31 K.oTmp :: slotAt .r4 .r25 (oPoly 0) ++ slotAt .r5 .r25 (oPoly K.k) ++
      [.addi .r6 .r31 K.oNtt])) s fun s' =>
      Only s s' ∧ s'.gpr .r3 = P + BitVec.ofNat 64 K.oTmp ∧
      s'.gpr .r4 = P + BitVec.ofNat 64 j <<< 10 + BitVec.ofNat 64 (oPoly 0) ∧
      s'.gpr .r5 = P + BitVec.ofNat 64 j <<< 10 + BitVec.ofNat 64 (oPoly K.k) ∧
      s'.gpr .r6 = P + BitVec.ofNat 64 K.oNtt := by
  have e1 : K.oTmp < 32768 := oTmp_lt hK
  have e2 : oPoly K.k < 32768 := oPolyK_lt hK
  have e3 : K.oNtt < 32768 := oNtt_lt hK
  have e4 : oPoly 0 < 32768 := by decide
  prun [slotAt, List.cons_append, List.nil_append, List.append_assoc, e1, e2, e3, e4, h31, h25]
  exact ⟨Only.of_writes rfl rfl rfl rfl (by pres_tac), trivial⟩

/-- What `dot` changes: polynomials `3k + 2` and `3k + 3`, and the working space of the callees. -/
abbrev dotW (K : KemLay) : List (Nat × Nat × Nat) := [(0, K.oAcc, 2048), (0, K.oNtt, 1024)]

/-- After the first `j` products. -/
structure DotInv (K : KemLay) (L : Lay) (a v : Nat → Poly) (s₀ : State) (j : Nat) (s : State) : Prop where
  kx : KeptX [.r25] (L.RL (dotW K)) s₀ s
  r25 : s.gpr .r25 = BitVec.ofNat 64 j
  acc : PolyIs s.mem (L.A 0 K.oAcc) (rowAcc a v j)

/-- The polynomials of the operands apart from what `dot` changes. -/
abbrev DotWVec (K : KemLay) : Prop := ∀ j < 2 * K.k, (dotW K).all (sep0 (oPoly j) 1024) = true

theorem dotW_vec {K : KemLay} (hK : K.WF) : DotWVec K :=
  (by decide : ∀ k < 5, DotWVec (kOf k)) K.k (by have := hK.k4; omega)

/-- In `dotBody`, after the product. -/
structure DB (K : KemLay) (L : Lay) (a v : Nat → Poly) (s₀ : State) (j : Nat) (s : State) : Prop where
  kx : KeptX [.r25] (L.RL (dotW K)) s₀ s
  r25 : s.gpr .r25 = BitVec.ofNat 64 j
  acc : PolyIs s.mem (L.A 0 K.oAcc) (rowAcc a v j)
  tmp : PolyIs s.mem (L.A 0 K.oTmp) (multiplyNTTs (a j) (v j))

/-- In `dotBody`, after the sum. -/
structure DC (K : KemLay) (L : Lay) (a v : Nat → Poly) (s₀ : State) (j : Nat) (s : State) : Prop where
  kx : KeptX [.r25] (L.RL (dotW K)) s₀ s
  r25 : s.gpr .r25 = BitVec.ofNat 64 j
  acc : PolyIs s.mem (L.A 0 K.oAcc) (rowAcc a v (j + 1))

section
variable {K : KemLay} (hK : K.WF) {L : Lay} {a v : Nat → Poly} {s₀ : State} (hc₀ : Ctx L s₀)
    (ha : ∀ j < K.k, PolyIs s₀.mem (L.A 0 (oPoly j)) (a j))
    (hv : ∀ j < K.k, PolyIs s₀.mem (L.A 0 (oPoly (K.k + j))) (v j))
    {j : Nat} (hj : j < K.k) {s : State} (h : DotInv K L a v s₀ j s)
include hK hc₀ ha hv hj h

omit ha hv in
theorem dot1_ok : WP isa (.block (.addi .r3 .r31 K.oTmp :: slotAt .r4 .r25 (oPoly 0) ++ slotAt .r5 .r25 (oPoly K.k) ++
      [.addi .r6 .r31 K.oNtt])) s fun s₁ => Only s s₁ ∧ s₁.gpr .r3 = L.A 0 K.oTmp ∧
      s₁.gpr .r4 = L.A 0 (oPoly j) ∧ s₁.gpr .r5 = L.A 0 (oPoly (K.k + j)) ∧ s₁.gpr .r6 = L.A 0 K.oNtt := by
  have hc := h.kx.ctx (by decide) hc₀
  have eo : oPoly (K.k + j) = oPoly K.k + 1024 * j := by simp only [oPoly]; omega
  have eo' : oPoly j = oPoly 0 + 1024 * j := by simp only [oPoly]; try omega
  refine WP.mono (dotArgs_ok hK hc.r31 h.r25) fun s₁ ⟨o₁, m3, m4, m5, m6⟩ => ⟨o₁, m3, ?_, ?_, m6⟩
  · rw [m4, slot_eq _ (by offs), ← eo']
  · rw [m5, slot_eq _ (by offs), ← eo]

theorem dot2_ok {s₁ : State} (o₁ : Only s s₁) (m3 : s₁.gpr .r3 = L.A 0 K.oTmp)
    (m4 : s₁.gpr .r4 = L.A 0 (oPoly j)) (m5 : s₁.gpr .r5 = L.A 0 (oPoly (K.k + j)))
    (m6 : s₁.gpr .r6 = L.A 0 K.oNtt) : WP isa callMul s₁ (DB K L a v s₀ j) := by
  have hL := hc₀.ok
  have hc := h.kx.ctx (by decide) hc₀
  have as : PolyIs s.mem (L.A 0 (oPoly j)) (a j) :=
    Lay.polyIs_keep hL h.kx.frame (hc₀.sepAll0 (by offs) (dotW_vec hK j (by omega))) (ha j hj)
  have vs : PolyIs s.mem (L.A 0 (oPoly (K.k + j))) (v j) :=
    Lay.polyIs_keep hL h.kx.frame (hc₀.sepAll0 (by offs) (dotW_vec hK (K.k + j) (by omega))) (hv j hj)
  have hc₁ := hc.only o₁
  refine mulL hL m3 m4 m5 m6 (hc.sep00 (by offs) (by offs) (by offs)) (hc.sep00 (by offs) (by offs) (by offs))
    (hc.sep00 (by offs) (by offs) (by offs)) (hc.sep00 (by offs) (by offs) (by offs))
    (hc.sep00 (by offs) (by offs) (by offs)) hc₁.cw (mem_rd_wr hc₁.cw) (mem_rd_wr hc₁.cw) hc₁.cw
    (by rw [o₁.mem]; exact as) (by rw [o₁.mem]; exact vs) fun s₂ k₂ p₂ => ⟨?_, ?_, ?_, p₂⟩
  · exact h.kx.trans ((o₁.x _ _).trans ((k₂.x _).subL hc₀ (by kdecide)))
  · rw [k₂.cs .r25 (by decide), o₁.cs .r25 (by decide), h.r25]
  · refine Lay.polyIs_keep hL k₂.frame (hc.sepAll0 (by kdecide) (by kdecide)) ?_
    rw [o₁.mem]; exact h.acc

omit ha hv hj h in
theorem dot3_ok {s₂ : State} (r : DB K L a v s₀ j s₂) :
    WP isa (.block [.addi .r3 .r31 K.oAcc, .addi .r4 .r31 K.oTmp]) s₂ fun s₃ => DB K L a v s₀ j s₃ ∧
      s₃.gpr .r3 = L.A 0 K.oAcc ∧ s₃.gpr .r4 = L.A 0 K.oTmp := by
  have hc := r.kx.ctx (by decide) hc₀
  exact WP.mono (accArgs_ok hc.r31 (oAcc_lt hK) (oTmp_lt hK)) fun s₃ ⟨o₃, a3, a4⟩ =>
    ⟨⟨r.kx.trans (o₃.x _ _), by rw [o₃.cs .r25 (by decide), r.r25], by rw [o₃.mem]; exact r.acc,
      by rw [o₃.mem]; exact r.tmp⟩, a3, a4⟩

omit ha hv hj h in
theorem dot4_ok {s₃ : State} (r : DB K L a v s₀ j s₃) (a3 : s₃.gpr .r3 = L.A 0 K.oAcc)
    (a4 : s₃.gpr .r4 = L.A 0 K.oTmp) : WP isa callAdd s₃ (DC K L a v s₀ j) := by
  have hc := r.kx.ctx (by decide) hc₀
  exact addL hc₀.ok a3 a4 (hc.sep00 (by kdecide) (by kdecide) (by kdecide)) hc.cw (mem_rd_wr hc.cw)
    r.acc r.tmp fun s₄ k₄ p₄ => ⟨r.kx.trans ((k₄.x _).subL hc₀ (by kdecide)),
      by rw [k₄.cs .r25 (by decide), r.r25], p₄⟩

omit hc₀ ha hv h in
theorem dot5_ok {s₄ : State} (r : DC K L a v s₀ j s₄) :
    WP isa (.block (count .r25 K.k)) s₄ fun s' =>
      DotInv K L a v s₀ (j + 1) s' ∧ (s'.gpr .r0 != 0) = decide (j + 1 ≠ K.k) := by
  have k4 := hK.k4
  exact WP.mono (count_ok (by decide) (by omega) (by omega) r.r25) fun s' ⟨k', g', z'⟩ =>
    ⟨⟨r.kx.trans (k'.mono (fun _ h => absurd h List.not_mem_nil)), g',
      polyIs_frame k'.frame (fun _ h => absurd h List.not_mem_nil) r.acc⟩, z'⟩

end

theorem dotBody_ok {K : KemLay} (hK : K.WF) {L : Lay} {a v : Nat → Poly} {s₀ : State} (hc₀ : Ctx L s₀)
    (ha : ∀ j < K.k, PolyIs s₀.mem (L.A 0 (oPoly j)) (a j))
    (hv : ∀ j < K.k, PolyIs s₀.mem (L.A 0 (oPoly (K.k + j))) (v j))
    {j : Nat} (hj : j < K.k) {s : State} (h : DotInv K L a v s₀ j s) :
    WP isa K.dotBody s fun s' => DotInv K L a v s₀ (j + 1) s' ∧ (s'.gpr .r0 != 0) = decide (j + 1 ≠ K.k) :=
  WP.seq (WP.mono (dot1_ok hK hc₀ hj h) fun _ ⟨o₁, m3, m4, m5, m6⟩ =>
    WP.seq (WP.mono (dot2_ok hK hc₀ ha hv hj h o₁ m3 m4 m5 m6) fun _ r₂ =>
    WP.seq (WP.mono (dot3_ok hK hc₀ r₂) fun _ ⟨r₃, a3, a4⟩ =>
    WP.seq (WP.mono (dot4_ok hK hc₀ r₃ a3 a4) fun _ r₄ => dot5_ok hK hj r₄))))

theorem dot_ok {K : KemLay} (hK : K.WF) {L : Lay} {a v : Nat → Poly} {s₀ : State} (hc₀ : Ctx L s₀)
    (ha : ∀ j < K.k, PolyIs s₀.mem (L.A 0 (oPoly j)) (a j))
    (hv : ∀ j < K.k, PolyIs s₀.mem (L.A 0 (oPoly (K.k + j))) (v j)) :
    WP isa K.dot s₀ fun s => KeptX [.r25] (L.RL (dotW K)) s₀ s ∧
      PolyIs s.mem (L.A 0 K.oAcc) (VG.Proof.MlKem.KPke.dotK a v K.k) := by
  refine WP.seq (WP.mono (zeroPoly_ok hc₀ (by offs)) fun s₁ ⟨k₁, z₁⟩ => ?_)
  refine WP.seq (WP.mono (li_ok .r25 (N := 0) (by decide)) fun s₂ ⟨k₂, g₂, m₂⟩ => ?_)
  refine wp_loop_nz (DotInv K L a v s₀) (N := K.k) (by have := hK.k1; omega)
    (fun j hj s h => dotBody_ok hK hc₀ ha hv hj h)
    (fun _ h => ⟨h.kx, by rw [← rowAcc_eq]; exact h.acc⟩)
    ⟨((k₁.x _).subL hc₀ (by kdecide)).trans (k₂.mono (fun _ h => absurd h List.not_mem_nil)), g₂,
      by rw [m₂]; exact z₁⟩

end VG.Proof.MlKem.PPC64LE

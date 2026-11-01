module

public import VerifiedGarbage.Proof.MlKem.RISCV64.Prf
import VerifiedGarbage.Proof.MlKem.RISCV64.Loops
import VerifiedGarbage.Proof.MlKem.RISCV64.HashTop
import VerifiedGarbage.Proof.MlKem.RISCV64.Common
import VerifiedGarbage.Proof.MlKem.RISCV64.Sample
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Wp
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on RISC-V: a row of `Â ∘ v̂`

As on PPC64LE (`Proof/MlKem/PPC64LE/RowSum.lean`). `K.rowSum transpose` sums,
in polynomial `3k + 2`, the products of the entries `j < k` (in `s5`) of row
`i` (in `s6`) of `Â` (or of `Â^⊺`, `transpose`) with polynomials `k + j`,
sampling each entry into polynomial `3k + 4` from the seed `ρ ‖ j ‖ i`
(`ρ ‖ i ‖ j`) at 1248. If a `SampleNTT` does not finish, the product uses
polynomial `k + j` in its place (`effA`), and the flag in `s4` becomes 0
(`rowSum_ok`). The sum is `KPke.dotK` (`rowAcc_eq`). `K.dot` sums the
products of polynomials `j` and `k + j` (`dot_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.RISCV64

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64
open VG.RISCV64.Wp
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

/-- Two polynomials' addresses. -/
theorem addr2_ok {s : State} {P : BitVec 64} {d d' : Reg} {j j' : Nat} (hj : j + 2 < 2048) (hj' : j' + 2 < 2048)
    (hd : d ∉ preserved) (hd' : d' ∉ preserved) (hdd : d ≠ d') (h11 : s.gpr .s11 = P) :
    WP isa (.block (polyAddr d j ++ polyAddr d' j')) s fun s' =>
      Only s s' ∧ s'.gpr d = P + BitVec.ofNat 64 (oPoly j) ∧ s'.gpr d' = P + BitVec.ofNat 64 (oPoly j') := by
  have n11 : d ≠ .s11 := fun e => hd (e ▸ by decide)
  have n11' : d' ≠ .s11 := fun e => hd' (e ▸ by decide)
  rw [← List.append_nil (polyAddr d' j')]
  exact wp_polyAddr hj n11 fun s₁ h₁ => wp_polyAddr hj' n11' fun s₂ h₂ => WP.block_nil
    ⟨(updOnly h₁ hd).trans (updOnly h₂ hd'), by rw [h₂.other _ hdd, h₁.gpr, h11],
      by rw [h₂.gpr, h₁.other _ (Ne.symm n11), h11]⟩

section
variable {K : KemLay} {s : State} {P : BitVec 64} {i j : Nat}

theorem seedArgs_ok (hK : K.WF) (transpose : Bool) (h11 : s.gpr .s11 = P) (h6 : s.gpr .s6 = BitVec.ofNat 64 i)
    (h5 : s.gpr .s5 = BitVec.ofNat 64 j) (hi : i < 256) (hj : j < 256)
    (w1 : InRegions s.wr (P + BitVec.ofNat 64 (oSeed + 32)) 1)
    (w2 : InRegions s.wr (P + BitVec.ofNat 64 (oSeed + 33)) 1) :
    WP isa (.block (seedBytes transpose ++ .addi .a0 .s11 oSeed :: polyAddr .a1 K.jAhat ++ polyAddr .a2 K.jSample))
      s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
        s'.mem = (s.mem.writeW (P + BitVec.ofNat 64 (oSeed + 32)) (BitVec.ofNat 8 (if transpose then i else j))).writeW
          (P + BitVec.ofNat 64 (oSeed + 33)) (BitVec.ofNat 8 (if transpose then j else i)) ∧
        s'.gpr .a0 = P + BitVec.ofNat 64 oSeed ∧ s'.gpr .a1 = P + BitVec.ofNat 64 K.oAhat ∧
        s'.gpr .a2 = P + BitVec.ofNat 64 K.oSample := by
  have k4 := hK.k4
  have si := setWidth8_ofNat (N := i) (by omega)
  have sj := setWidth8_ofNat (N := j) (by omega)
  rw [← List.append_nil (polyAddr .a2 K.jSample)]
  cases transpose <;>
  · simp only [seedBytes, Bool.false_eq_true, ite_true, ite_false, List.cons_append,
      List.nil_append]
    refine wp_sb (by decide) (by rw [h11]) w1 fun s₁ m₁ =>
      wp_sb (by decide) (by rw [m₁.gpr, h11]) (by rw [m₁.wr]; exact w2) fun s₂ m₂ =>
      wp_addi (by decide) fun s₃ h₃ => wp_polyAddr (by offs) (by decide) fun s₄ h₄ =>
      wp_polyAddr (by offs) (by decide) fun s₅ h₅ => WP.block_nil
        ⟨fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨-, n0, n1, n2, -, -⟩ := pres_ne hr
      rw [h₅.other _ n2, h₄.other _ n1, h₃.other _ n0, m₂.gpr, m₁.gpr]
    · rw [h₅.rd, h₄.rd, h₃.rd, m₂.rd, m₁.rd]
    · rw [h₅.wr, h₄.wr, h₃.wr, m₂.wr, m₁.wr]
    · rw [h₅.sp, h₄.sp, h₃.sp, m₂.sp, m₁.sp]
    · rw [h₅.mem, h₄.mem, h₃.mem, m₂.mem, m₁.mem, m₁.gpr, h5, h6, si, sj]
    · rw [h₅.other _ (by decide), h₄.other _ (by decide), h₃.gpr, m₂.gpr, m₁.gpr, h11]
    · rw [h₅.other _ (by decide), h₄.gpr, h₃.other _ (by decide), m₂.gpr, m₁.gpr, h11]
    · rw [h₅.gpr, h₄.other _ (by decide), h₃.other _ (by decide), m₂.gpr, m₁.gpr, h11]

theorem flag_ok {b c : Bool} (h3 : s.gpr .a0 = if c then 1 else 0) (h24 : s.gpr .s4 = if b then 1 else 0) :
    WP isa (.block [.logic .and .s4 .s4 .a0]) s fun s' =>
      KeptX [.s4] [] s s' ∧ s'.gpr .s4 = (if b && c then 1 else 0) ∧ s'.gpr .a0 = s.gpr .a0 ∧ s'.mem = s.mem :=
  wp_and fun s' u => WP.block_nil ⟨⟨fun r _ hx => u.other r fun e => hx (by rw [e]; exact List.mem_singleton_self _),
    u.sp, u.rd, u.wr, by rw [u.mem]; exact Frame.refl _ _⟩,
    by rw [u.gpr, h3, h24]; cases b <;> cases c <;> rfl, u.other _ (by decide), u.mem⟩

theorem selT_ok (hK : K.WF) (h11 : s.gpr .s11 = P) (hj : j < K.k) (h5 : s.gpr .s5 = BitVec.ofNat 64 j) :
    WP isa (.block (slotAt .a1 .s5 K.k)) s fun s' =>
      Only s s' ∧ s'.gpr .a1 = P + BitVec.ofNat 64 (oPoly (K.k + j)) := by
  have k4 := hK.k4
  rw [← List.append_nil (slotAt .a1 .s5 K.k)]
  exact wp_slotAt (i := j) (by omega) (by omega) (by decide) h5 fun s' h => WP.block_nil
    ⟨updOnly h (by decide), by rw [h.gpr, h11]; unfold oPoly; congr 2; omega⟩

theorem selF_ok (hK : K.WF) (h11 : s.gpr .s11 = P) :
    WP isa (.block (polyAddr .a1 K.jAhat)) s fun s' => Only s s' ∧ s'.gpr .a1 = P + BitVec.ofNat 64 K.oAhat := by
  have k4 := hK.k4
  rw [← List.append_nil (polyAddr .a1 K.jAhat)]
  exact wp_polyAddr (by offs) (by decide) fun s' h => WP.block_nil ⟨updOnly h (by decide), by rw [h.gpr, h11]⟩

theorem mulArgs_ok (hK : K.WF) (h11 : s.gpr .s11 = P) (hj : j < K.k) (h5 : s.gpr .s5 = BitVec.ofNat 64 j) :
    WP isa (.block (polyAddr .a0 K.jTmp ++ slotAt .a2 .s5 K.k ++ polyAddr .a3 K.jNtt)) s fun s' =>
      Only s s' ∧ s'.gpr .a0 = P + BitVec.ofNat 64 K.oTmp ∧ s'.gpr .a1 = s.gpr .a1 ∧
      s'.gpr .a2 = P + BitVec.ofNat 64 (oPoly (K.k + j)) ∧
      s'.gpr .a3 = P + BitVec.ofNat 64 K.oNtt := by
  have k4 := hK.k4
  rw [← List.append_nil (polyAddr .a3 K.jNtt), List.append_assoc]
  refine wp_polyAddr (by offs) (by decide) fun s₁ h₁ =>
    wp_slotAt (i := j) (by omega) (by omega) (by decide) (by rw [h₁.other _ (by decide), h5]) fun s₂ h₂ =>
    wp_polyAddr (by offs) (by decide) fun s₃ h₃ => WP.block_nil
      ⟨(updOnly h₁ (by decide)).trans ((updOnly h₂ (by decide)).trans (updOnly h₃ (by decide))), ?_, ?_, ?_, ?_⟩
  · rw [h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr, h11]
  · rw [h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide)]
  · rw [h₃.other _ (by decide), h₂.gpr, h₁.other _ (by decide), h11]; unfold oPoly; congr 2; omega
  · rw [h₃.gpr, h₂.other _ (by decide), h₁.other _ (by decide), h11]

end

/-! ## The loop -/

/-- What a row needs of the state it starts from. -/
structure RowPre (K : KemLay) (L : Lay) (ρ : List Byte) (v : Nat → Poly) (i : Nat) (fl : Bool) (s : State) : Prop where
  wf : K.WF
  ctx : Ctx L s
  ik : i < K.k
  s6 : s.gpr .s6 = BitVec.ofNat 64 i
  s4 : s.gpr .s4 = if fl then 1 else 0
  rho : bytesAt s.mem (L.A 0 oSeed) 32 = ρ
  vec : ∀ j < K.k, PolyIs s.mem (L.A 0 (oPoly (K.k + j))) (v j)

/-- What a row changes: the indices of the seed, polynomials `3k + 2` to
`3k + 4`, the working space of the callees and the stack. -/
abbrev rowW (K : KemLay) : List (Nat × Nat × Nat) :=
  [(0, 1280, 2), (0, K.oAcc, 3072), (0, K.oSample, 3072), (1, 0, 1168)]

/-- After the first `j` entries of the row. -/
structure RowInv (K : KemLay) (L : Lay) (transpose : Bool) (ρ : List Byte) (v : Nat → Poly) (i : Nat) (fl : Bool)
    (s₀ : State) (j : Nat) (s : State) : Prop where
  kx : KeptX [.s5, .s4] (L.RL (rowW K)) s₀ s
  s5 : s.gpr .s5 = BitVec.ofNat 64 j
  s4 : s.gpr .s4 = if fl && okRow transpose ρ i j then 1 else 0
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
  [((0 : Nat), K.oAhat, (1024 : Nat)), (0, K.oSample, 2048), (1, 0, 1168)].all (fun w => (rowW K).any (subB0 w)) = true ∧
  [((0 : Nat), K.oAhat, (1024 : Nat)), (0, K.oSample, 2048), (1, 0, 1168)].all (sep0 K.oAcc 1024) = true ∧
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
  kx : KeptX [.s5, .s4] (L.RL (rowW K)) s₀ s
  s5 : s.gpr .s5 = BitVec.ofNat 64 j
  acc : PolyIs s.mem (L.A 0 K.oAcc) (rowAcc (fun j => effA transpose ρ i j (v j)) v j)

/-- After the seed and the arguments of `SampleNTT`. -/
structure RA (s : State) : Prop where
  rs : RS K L transpose ρ v i s₀ j s
  s4 : s.gpr .s4 = if fl && okRow transpose ρ i j then 1 else 0
  a0 : s.gpr .a0 = L.A 0 oSeed
  a1 : s.gpr .a1 = L.A 0 K.oAhat
  a2 : s.gpr .a2 = L.A 0 K.oSample
  seed : bytesAt s.mem (L.A 0 oSeed) 34 = rowSeed transpose ρ i j

/-- After `SampleNTT`. -/
structure RB (s : State) : Prop where
  rs : RS K L transpose ρ v i s₀ j s
  s4 : s.gpr .s4 = if fl && okRow transpose ρ i j then 1 else 0
  a0 : s.gpr .a0 = if cOk transpose ρ i j then 1 else 0
  ahat : ∀ a, sampleNTT 280 (rowSeed transpose ρ i j) = some a → PolyIs s.mem (L.A 0 K.oAhat) a

/-- After the flag. -/
structure RC (s : State) : Prop where
  rs : RS K L transpose ρ v i s₀ j s
  s4 : s.gpr .s4 = if fl && okRow transpose ρ i (j + 1) then 1 else 0
  a0 : s.gpr .a0 = if cOk transpose ρ i j then 1 else 0
  ahat : ∀ a, sampleNTT 280 (rowSeed transpose ρ i j) = some a → PolyIs s.mem (L.A 0 K.oAhat) a

/-- After the selection of the entry. -/
structure RD (s : State) : Prop where
  rs : RS K L transpose ρ v i s₀ j s
  s4 : s.gpr .s4 = if fl && okRow transpose ρ i (j + 1) then 1 else 0
  a1 : s.gpr .a1 = L.A 0 (oSel K (cOk transpose ρ i j) j)
  sel : PolyIs s.mem (L.A 0 (oSel K (cOk transpose ρ i j) j)) (effA transpose ρ i j (v j))

/-- After the arguments of the product. -/
structure RE (s : State) : Prop where
  rd : RD K L transpose ρ v i fl s₀ j s
  a0 : s.gpr .a0 = L.A 0 K.oTmp
  a2 : s.gpr .a2 = L.A 0 (oPoly (K.k + j))
  a3 : s.gpr .a3 = L.A 0 K.oNtt

/-- After the product. -/
structure RF (s : State) : Prop where
  rs : RS K L transpose ρ v i s₀ j s
  s4 : s.gpr .s4 = if fl && okRow transpose ρ i (j + 1) then 1 else 0
  tmp : PolyIs s.mem (L.A 0 K.oTmp) (multiplyNTTs (effA transpose ρ i j (v j)) (v j))

/-- After the arguments of the sum. -/
structure RG (s : State) : Prop where
  rf : RF K L transpose ρ v i fl s₀ j s
  a0 : s.gpr .a0 = L.A 0 K.oAcc
  a1 : s.gpr .a1 = L.A 0 K.oTmp

/-- After the sum. -/
structure RH (s : State) : Prop where
  kx : KeptX [.s5, .s4] (L.RL (rowW K)) s₀ s
  s5 : s.gpr .s5 = BitVec.ofNat 64 j
  s4 : s.gpr .s4 = if fl && okRow transpose ρ i (j + 1) then 1 else 0
  acc : PolyIs s.mem (L.A 0 K.oAcc) (rowAcc (fun j => effA transpose ρ i j (v j)) v (j + 1))

end

section
variable {K : KemLay} {L : Lay} {transpose : Bool} {ρ : List Byte} {v : Nat → Poly} {i : Nat} {fl : Bool}
  {s₀ : State} {j : Nat}

theorem RS.ctx (hp : RowPre K L ρ v i fl s₀) {s : State} (h : RS K L transpose ρ v i s₀ j s) : Ctx L s :=
  h.kx.ctx (by decide) hp.ctx

theorem RS.s6 (hp : RowPre K L ρ v i fl s₀) {s : State} (h : RS K L transpose ρ v i s₀ j s) :
    s.gpr .s6 = BitVec.ofNat 64 i := by
  rw [h.kx.cs .s6 (by decide) (by decide), hp.s6]

theorem RS.vec (hp : RowPre K L ρ v i fl s₀) (hj : j < K.k) {s : State} (h : RS K L transpose ρ v i s₀ j s) :
    PolyIs s.mem (L.A 0 (oPoly (K.k + j))) (v j) := by
  have hK := hp.wf
  exact Lay.polyIs_keep hp.ctx.ok h.kx.frame (hp.ctx.sepAll0 (by offs) (rowW_vec hp.wf j hj)) (hp.vec j hj)

/-- A step that keeps `RS`: it changes only the regions of `rowW K` and not `s5`, nor the sum. -/
theorem RS.step (hp : RowPre K L ρ v i fl s₀) {s s' : State} (h : RS K L transpose ρ v i s₀ j s) {xs : List Reg}
    {W : List (Nat × Nat × Nat)} (hk : KeptX xs (L.RL W) s s') (hx : ∀ x ∈ xs, x ∈ [Reg.s5, .s4])
    (h25 : Reg.s5 ∉ xs) (hW : W.all (fun w => (rowW K).any (subB0 w)) = true)
    (hA : sepAll L.sizes (0, K.oAcc, 1024) W = true) : RS K L transpose ρ v i s₀ j s' :=
  ⟨h.kx.trans ((hk.weaken hx).subL hp.ctx hW), by rw [hk.cs .s5 (by decide) h25, h.s5],
    Lay.polyIs_keep hp.ctx.ok hk.frame hA h.acc⟩

theorem rowA_ok (hp : RowPre K L ρ v i fl s₀) (hj : j < K.k) {s : State}
    (h : RowInv K L transpose ρ v i fl s₀ j s) :
    WP isa (.block (seedBytes transpose ++ .addi .a0 .s11 oSeed :: polyAddr .a1 K.jAhat ++ polyAddr .a2 K.jSample))
      s (RA K L transpose ρ v i fl s₀ j) := by
  have hK := hp.wf
  have k4 := hK.k4
  have hL := hp.ctx.ok
  have hi := hp.ik
  have hc := h.kx.ctx (by decide) hp.ctx
  have g6 : s.gpr .s6 = BitVec.ofNat 64 i := by rw [h.kx.cs .s6 (by decide) (by decide), hp.s6]
  have ρs : bytesAt s.mem (L.A 0 oSeed) 32 = ρ := by
    rw [← hp.rho]; exact Lay.bytes_keep hL h.kx.frame (hp.ctx.sepAll0 (by decide) (row_lf hK).1) (by decide)
  have w1 : InRegions s.wr (L.ptr 0 + BitVec.ofNat 64 (oSeed + 32)) 1 :=
    hc.cs (o := 1280) (l := 1) (by decide) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  have w2 : InRegions s.wr (L.ptr 0 + BitVec.ofNat 64 (oSeed + 33)) 1 :=
    hc.cs (o := 1281) (l := 1) (by decide) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  refine WP.mono (seedArgs_ok hK transpose hc.s11 g6 h.s5 (by omega) (by omega) w1 w2)
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
    by rw [k₁.cs .s5 (by decide) (by decide), h.s5],
    Lay.polyIs_keep hL k₁.frame (hc.sepAll0 (row_lf hK).2.2.1 (row_lf hK).2.2.2.1) h.acc⟩,
    by rw [k₁.cs .s4 (by decide) (by decide), h.s4], g3, g4, g5, ?_⟩
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
  refine sampleL hc h.a0 h.a1 h.a2 (hc.sep00 (by decide) lf.2.2.2.2.1 lf.2.2.2.2.2.1)
    (hc.sep00 (by decide) lf.2.2.2.2.2.2.1 lf.2.2.2.2.2.2.2.1)
    (hc.sep00 lf.2.2.2.2.1 lf.2.2.2.2.2.2.1 lf.2.2.2.2.2.2.2.2.1)
    (hc.sep01 (by decide) (by decide)) (hc.sep01 lf.2.2.2.2.1 (by decide)) (hc.sep01 lf.2.2.2.2.2.2.1 (by decide))
    (mem_rd_wr hc.cw) hc.cw hc.cw (hc.alP _) (hc.alP _) fun s' k' r3' a' => ?_
  rw [h.seed] at r3' a'
  exact ⟨h.rs.step hp (k'.x []) (by simp) (by simp) lf.2.2.2.2.2.2.2.2.2.1
      (hc.sepAll0 lf.2.2.1 lf.2.2.2.2.2.2.2.2.2.2.1),
    by rw [k'.cs .s4 (by decide), h.s4], r3', a'⟩

theorem rowC_ok {s : State} (hp : RowPre K L ρ v i fl s₀) (h : RB K L transpose ρ v i fl s₀ j s) :
    WP isa (.block [.logic .and .s4 .s4 .a0]) s (RC K L transpose ρ v i fl s₀ j) :=
  WP.mono (flag_ok h.a0 h.s4) fun s' ⟨k', f', g3', m'⟩ =>
    ⟨h.rs.step hp (W := []) k' (by simp) (by decide) rfl rfl,
      by rw [f', Bool.and_assoc, ← okRow_succ], by rw [g3', h.a0], by rw [m']; exact h.ahat⟩

theorem rowD_ok (hp : RowPre K L ρ v i fl s₀) (hj : j < K.k) {s : State} (h : RC K L transpose ρ v i fl s₀ j s) :
    WP isa (.ite (.zero .a0) (.block (slotAt .a1 .s5 K.k)) (.block (polyAddr .a1 K.jAhat))) s
      (RD K L transpose ρ v i fl s₀ j) := by
  have hK := hp.wf
  have hc := h.rs.ctx hp
  refine WP.ite (s.gpr .a0 == 0) (eval_zero _ _) (fun hz => WP.mono (selT_ok hK hc.s11 hj h.rs.s5)
    fun s₄ ⟨o₄, g4₄⟩ => ?_) (fun hz => WP.mono (selF_ok hK hc.s11) fun s₄ ⟨o₄, g4₄⟩ => ?_)
  · have hc' : cOk transpose ρ i j = false := by
      rw [h.a0] at hz; cases e : cOk transpose ρ i j <;> simp_all
    have e : effA transpose ρ i j (v j) = v j := by
      simp only [effA]
      simp only [cOk] at hc'
      cases e' : sampleNTT 280 (rowSeed transpose ρ i j)
      · rfl
      · rw [e'] at hc'; cases hc'
    refine ⟨h.rs.step hp (o₄.x [] []) (W := []) (by simp) (by simp) rfl rfl,
      by rw [o₄.cs .s4 (by decide), h.s4], by rw [g4₄, hc']; rfl, ?_⟩
    rw [hc', e, o₄.mem]; exact h.rs.vec hp hj
  · have hc' : cOk transpose ρ i j = true := by
      rw [h.a0] at hz; cases e : cOk transpose ρ i j <;> simp_all
    refine ⟨h.rs.step hp (o₄.x [] []) (W := []) (by simp) (by simp) rfl rfl,
      by rw [o₄.cs .s4 (by decide), h.s4], by rw [g4₄, hc']; rfl, ?_⟩
    simp only [cOk] at hc'
    cases e' : sampleNTT 280 (rowSeed transpose ρ i j) with
    | none => rw [e'] at hc'; cases hc'
    | some a =>
      have e : effA transpose ρ i j (v j) = a := by simp only [effA, e', Option.getD_some]
      rw [e, o₄.mem, show oSel K (cOk transpose ρ i j) j = K.oAhat by simp [cOk, e']]
      exact h.ahat a e'

theorem rowE_ok (hp : RowPre K L ρ v i fl s₀) (hj : j < K.k) {s : State} (h : RD K L transpose ρ v i fl s₀ j s) :
    WP isa (.block (polyAddr .a0 K.jTmp ++ slotAt .a2 .s5 K.k ++ polyAddr .a3 K.jNtt)) s
      (RE K L transpose ρ v i fl s₀ j) := by
  have hK := hp.wf
  have hc := h.rs.ctx hp
  refine WP.mono (mulArgs_ok (j := j) hK hc.s11 hj h.rs.s5) fun s' ⟨o', m3, m4, m5, m6⟩ => ?_
  exact ⟨⟨h.rs.step hp (o'.x [] []) (W := []) (by simp) (by simp) rfl rfl,
    by rw [o'.cs .s4 (by decide), h.s4], by rw [m4, h.a1], by rw [o'.mem]; exact h.sel⟩, m3, m5, m6⟩

theorem sel_sep (hK : K.WF) (c : Bool) {j : Nat} (hj : j < K.k) :
    oSel K c j + 1024 ≤ 32768 ∧ (K.oTmp + 1024 ≤ oSel K c j ∨ oSel K c j + 1024 ≤ K.oTmp) ∧
      (oSel K c j + 1024 ≤ K.oNtt ∨ K.oNtt + 1024 ≤ oSel K c j) := by
  cases c <;> simp only [oSel, Bool.false_eq_true, ite_false, ite_true] <;> offs

theorem sel_al {L : Lay} {s : State} (hc : Ctx L s) (c : Bool) (j : Nat) : L.Al 0 (oSel K c j) := by
  cases c
  · exact hc.alP _
  · exact hc.alP _

theorem rowF_ok (hp : RowPre K L ρ v i fl s₀) (hj : j < K.k) {s : State} (h : RE K L transpose ρ v i fl s₀ j s) :
    WP isa callMul s (RF K L transpose ρ v i fl s₀ j) := by
  have hK := hp.wf
  have hc := h.rd.rs.ctx hp
  have lf := row_lf hK
  obtain ⟨s1, s2, s3⟩ := sel_sep hK (cOk transpose ρ i j) hj
  refine mulL hc.ok h.a0 h.rd.a1 h.a2 h.a3 (hc.sep00 (by offs) s1 s2) (hc.sep00 (by offs) (by offs) (by offs))
    (hc.sep00 (by offs) (by offs) (by offs)) (hc.sep00 s1 (by offs) s3) (hc.sep00 (by offs) (by offs) (by offs))
    hc.cw (mem_rd_wr hc.cw) (mem_rd_wr hc.cw) hc.cw h.rd.sel (h.rd.rs.vec hp hj)
    (hc.alP _) (sel_al hc _ _) (hc.alP _) (hc.alP _) fun s' k' p' => ?_
  exact ⟨h.rd.rs.step hp (k'.x []) (by simp) (by simp) lf.2.2.2.2.2.2.2.2.2.2.2.1
      (hc.sepAll0 lf.2.2.1 lf.2.2.2.2.2.2.2.2.2.2.2.2.1),
    by rw [k'.cs .s4 (by decide), h.rd.s4], p'⟩

theorem rowG_ok (hp : RowPre K L ρ v i fl s₀) {s : State} (h : RF K L transpose ρ v i fl s₀ j s) :
    WP isa (.block (polyAddr .a0 K.jAcc ++ polyAddr .a1 K.jTmp)) s (RG K L transpose ρ v i fl s₀ j) := by
  have hK := hp.wf
  have k4 := hK.k4
  have hc := h.rs.ctx hp
  exact WP.mono (addr2_ok (by offs) (by offs) (by decide) (by decide) (by decide) hc.s11) fun s' ⟨o', a3, a4⟩ =>
    ⟨⟨h.rs.step hp (o'.x [] []) (W := []) (by simp) (by simp) rfl rfl,
      by rw [o'.cs .s4 (by decide), h.s4], by rw [o'.mem]; exact h.tmp⟩, a3, a4⟩

theorem rowH_ok (hp : RowPre K L ρ v i fl s₀) {s : State} (h : RG K L transpose ρ v i fl s₀ j s) :
    WP isa callAdd s (RH K L transpose ρ v i fl s₀ j) := by
  have hK := hp.wf
  have hc := h.rf.rs.ctx hp
  have lf := row_lf hK
  refine addL hc.ok h.a0 h.a1 (hc.sep00 lf.2.2.1 lf.2.2.2.2.2.2.2.2.2.2.2.2.2.1 lf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    hc.cw (mem_rd_wr hc.cw) h.rf.rs.acc h.rf.tmp (hc.alP _) (hc.alP _) fun s' k' p' => ?_
  exact ⟨h.rf.rs.kx.trans ((k'.x _).subL hp.ctx lf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2),
    by rw [k'.cs .s5 (by decide), h.rf.rs.s5], by rw [k'.cs .s4 (by decide), h.rf.s4], p'⟩

theorem rowI_ok (hK : K.WF) {s : State} (hj : j < K.k) (h : RH K L transpose ρ v i fl s₀ j s) :
    WP isa (.block (count .s5 K.k)) s fun s' =>
      RowInv K L transpose ρ v i fl s₀ (j + 1) s' ∧ (s'.gpr .t0 != 0) = decide (j + 1 ≠ K.k) := by
  have k4 := hK.k4
  exact WP.mono (count_ok (by decide) (by omega) (by omega) h.s5) fun s' ⟨k', g', z'⟩ =>
    ⟨⟨h.kx.trans ((k'.weaken (by simp)).mono (fun _ h => absurd h List.not_mem_nil)), g',
      by rw [k'.cs .s4 (by decide) (by decide), h.s4],
      polyIs_frame k'.frame (fun _ h => absurd h List.not_mem_nil) h.acc⟩, z'⟩

theorem rowBody_ok (hp : RowPre K L ρ v i fl s₀) (hj : j < K.k) {s : State}
    (h : RowInv K L transpose ρ v i fl s₀ j s) :
    WP isa (K.rowBody transpose) s fun s' =>
      RowInv K L transpose ρ v i fl s₀ (j + 1) s' ∧ (s'.gpr .t0 != 0) = decide (j + 1 ≠ K.k) :=
  WP.seq (WP.mono (rowA_ok hp hj h) fun _ h₁ => WP.seq (WP.mono (rowB_ok hp h₁) fun _ h₂ =>
    WP.seq (WP.mono (rowC_ok hp h₂) fun _ h₃ => WP.seq (WP.mono (rowD_ok hp hj h₃) fun _ h₄ =>
    WP.seq (WP.mono (rowE_ok hp hj h₄) fun _ h₅ => WP.seq (WP.mono (rowF_ok hp hj h₅) fun _ h₆ =>
    WP.seq (WP.mono (rowG_ok hp h₆) fun _ h₇ => WP.seq (WP.mono (rowH_ok hp h₇) fun _ h₈ =>
      rowI_ok hp.wf hj h₈))))))))

end

theorem li_ok {s : State} (c : Reg) {N : Nat} (he : N < 2048) :
    WP isa (.block [.li c N]) s fun s' =>
      KeptX [c] [] s s' ∧ s'.gpr c = BitVec.ofNat 64 N ∧ s'.mem = s.mem :=
  wp_li he fun s' h => WP.block_nil ⟨⟨fun r _ hx => h.other r fun e => hx (by rw [e]; exact List.mem_singleton_self _),
    h.sp, h.rd, h.wr, by rw [h.mem]; exact Frame.refl _ _⟩, h.gpr, h.mem⟩

theorem rowSum_ok {K : KemLay} {L : Lay} {transpose : Bool} {ρ : List Byte} {v : Nat → Poly} {i : Nat}
    {fl : Bool} {s₀ : State} (hp : RowPre K L ρ v i fl s₀) :
    WP isa (K.rowSum transpose) s₀ (RowInv K L transpose ρ v i fl s₀ K.k) := by
  have hK := hp.wf
  have lf := row_lf hK
  refine WP.seq (WP.mono (zeroPoly_ok hp.ctx lf.2.2.1) fun s₁ ⟨k₁, z₁⟩ => ?_)
  refine WP.seq (WP.mono (li_ok .s5 (N := 0) (by decide)) fun s₂ ⟨k₂, g₂, m₂⟩ => ?_)
  refine wp_loop_nz (RowInv K L transpose ρ v i fl s₀) (N := K.k) (by have := hK.k1; omega)
    (fun j hj s h => rowBody_ok hp hj h) (fun _ h => h) ⟨?_, g₂, ?_, by rw [m₂]; exact z₁⟩
  · exact ((k₁.x _).subL hp.ctx lf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2).trans
      ((k₂.weaken (by simp)).mono (fun _ h => absurd h List.not_mem_nil))
  · rw [k₂.cs .s4 (by decide) (by decide), k₁.cs .s4 (by decide), hp.s4]
    simp [okRow]

/-! ## `dot` -/

theorem dotArgs_ok {K : KemLay} (hK : K.WF) {s : State} {P : BitVec 64} {j : Nat} (hj : j < K.k)
    (h11 : s.gpr .s11 = P) (h5 : s.gpr .s5 = BitVec.ofNat 64 j) :
    WP isa (.block (polyAddr .a0 K.jTmp ++ slotAt .a1 .s5 0 ++ slotAt .a2 .s5 K.k ++ polyAddr .a3 K.jNtt)) s
      fun s' => Only s s' ∧ s'.gpr .a0 = P + BitVec.ofNat 64 K.oTmp ∧
      s'.gpr .a1 = P + BitVec.ofNat 64 (oPoly j) ∧
      s'.gpr .a2 = P + BitVec.ofNat 64 (oPoly (K.k + j)) ∧
      s'.gpr .a3 = P + BitVec.ofNat 64 K.oNtt := by
  have k4 := hK.k4
  rw [← List.append_nil (polyAddr .a3 K.jNtt)]
  simp only [List.append_assoc]
  refine wp_polyAddr (by offs) (by decide) fun s₁ h₁ =>
    wp_slotAt (i := j) (by omega) (by omega) (by decide) (by rw [h₁.other _ (by decide), h5]) fun s₂ h₂ =>
    wp_slotAt (i := j) (by omega) (by omega) (by decide)
      (by rw [h₂.other _ (by decide), h₁.other _ (by decide), h5]) fun s₃ h₃ =>
    wp_polyAddr (by offs) (by decide) fun s₄ h₄ => WP.block_nil
      ⟨(updOnly h₁ (by decide)).trans ((updOnly h₂ (by decide)).trans ((updOnly h₃ (by decide)).trans
        (updOnly h₄ (by decide)))), ?_, ?_, ?_, ?_⟩
  · rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr, h11]
  · rw [h₄.other _ (by decide), h₃.other _ (by decide), h₂.gpr, h₁.other _ (by decide), h11]
  · rw [h₄.other _ (by decide), h₃.gpr, h₂.other _ (by decide), h₁.other _ (by decide), h11]
    unfold oPoly; congr 2; omega
  · rw [h₄.gpr, h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide), h11]

/-- What `dot` changes: polynomials `3k + 2` and `3k + 3`, and the working space of the callees. -/
abbrev dotW (K : KemLay) : List (Nat × Nat × Nat) := [(0, K.oAcc, 2048), (0, K.oNtt, 1024)]

/-- After the first `j` products. -/
structure DotInv (K : KemLay) (L : Lay) (a v : Nat → Poly) (s₀ : State) (j : Nat) (s : State) : Prop where
  kx : KeptX [.s5] (L.RL (dotW K)) s₀ s
  s5 : s.gpr .s5 = BitVec.ofNat 64 j
  acc : PolyIs s.mem (L.A 0 K.oAcc) (rowAcc a v j)

/-- The polynomials of the operands apart from what `dot` changes. -/
abbrev DotWVec (K : KemLay) : Prop := ∀ j < 2 * K.k, (dotW K).all (sep0 (oPoly j) 1024) = true

theorem dotW_vec {K : KemLay} (hK : K.WF) : DotWVec K :=
  (by decide : ∀ k < 5, DotWVec (kOf k)) K.k (by have := hK.k4; omega)

/-- In `dotBody`, after the product. -/
structure DB (K : KemLay) (L : Lay) (a v : Nat → Poly) (s₀ : State) (j : Nat) (s : State) : Prop where
  kx : KeptX [.s5] (L.RL (dotW K)) s₀ s
  s5 : s.gpr .s5 = BitVec.ofNat 64 j
  acc : PolyIs s.mem (L.A 0 K.oAcc) (rowAcc a v j)
  tmp : PolyIs s.mem (L.A 0 K.oTmp) (multiplyNTTs (a j) (v j))

/-- In `dotBody`, after the sum. -/
structure DC (K : KemLay) (L : Lay) (a v : Nat → Poly) (s₀ : State) (j : Nat) (s : State) : Prop where
  kx : KeptX [.s5] (L.RL (dotW K)) s₀ s
  s5 : s.gpr .s5 = BitVec.ofNat 64 j
  acc : PolyIs s.mem (L.A 0 K.oAcc) (rowAcc a v (j + 1))

section
variable {K : KemLay} (hK : K.WF) {L : Lay} {a v : Nat → Poly} {s₀ : State} (hc₀ : Ctx L s₀)
    (ha : ∀ j < K.k, PolyIs s₀.mem (L.A 0 (oPoly j)) (a j))
    (hv : ∀ j < K.k, PolyIs s₀.mem (L.A 0 (oPoly (K.k + j))) (v j))
    {j : Nat} (hj : j < K.k) {s : State} (h : DotInv K L a v s₀ j s)
include hK hc₀ ha hv hj h

omit ha hv in
theorem dot1_ok : WP isa (.block (polyAddr .a0 K.jTmp ++ slotAt .a1 .s5 0 ++ slotAt .a2 .s5 K.k ++
      polyAddr .a3 K.jNtt)) s fun s₁ =>
      Only s s₁ ∧ s₁.gpr .a0 = L.A 0 K.oTmp ∧
      s₁.gpr .a1 = L.A 0 (oPoly j) ∧ s₁.gpr .a2 = L.A 0 (oPoly (K.k + j)) ∧ s₁.gpr .a3 = L.A 0 K.oNtt := by
  have hc := h.kx.ctx (by decide) hc₀
  exact dotArgs_ok hK hj hc.s11 h.s5

theorem dot2_ok {s₁ : State} (o₁ : Only s s₁) (m3 : s₁.gpr .a0 = L.A 0 K.oTmp)
    (m4 : s₁.gpr .a1 = L.A 0 (oPoly j)) (m5 : s₁.gpr .a2 = L.A 0 (oPoly (K.k + j)))
    (m6 : s₁.gpr .a3 = L.A 0 K.oNtt) : WP isa callMul s₁ (DB K L a v s₀ j) := by
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
    (by rw [o₁.mem]; exact as) (by rw [o₁.mem]; exact vs) (hc.alP _) (hc.alP _) (hc.alP _) (hc.alP _)
    fun s₂ k₂ p₂ => ⟨?_, ?_, ?_, p₂⟩
  · exact h.kx.trans ((o₁.x _ _).trans ((k₂.x _).subL hc₀ (by kdecide)))
  · rw [k₂.cs .s5 (by decide), o₁.cs .s5 (by decide), h.s5]
  · refine Lay.polyIs_keep hL k₂.frame (hc.sepAll0 (by kdecide) (by kdecide)) ?_
    rw [o₁.mem]; exact h.acc

omit ha hv hj h in
theorem dot3_ok {s₂ : State} (r : DB K L a v s₀ j s₂) :
    WP isa (.block (polyAddr .a0 K.jAcc ++ polyAddr .a1 K.jTmp)) s₂ fun s₃ => DB K L a v s₀ j s₃ ∧
      s₃.gpr .a0 = L.A 0 K.oAcc ∧ s₃.gpr .a1 = L.A 0 K.oTmp := by
  have hc := r.kx.ctx (by decide) hc₀
  have k4 := hK.k4
  exact WP.mono (addr2_ok (by offs) (by offs) (by decide) (by decide) (by decide) hc.s11) fun s₃ ⟨o₃, a3, a4⟩ =>
    ⟨⟨r.kx.trans (o₃.x _ _), by rw [o₃.cs .s5 (by decide), r.s5], by rw [o₃.mem]; exact r.acc,
      by rw [o₃.mem]; exact r.tmp⟩, a3, a4⟩

omit ha hv hj h in
theorem dot4_ok {s₃ : State} (r : DB K L a v s₀ j s₃) (a3 : s₃.gpr .a0 = L.A 0 K.oAcc)
    (a4 : s₃.gpr .a1 = L.A 0 K.oTmp) : WP isa callAdd s₃ (DC K L a v s₀ j) := by
  have hc := r.kx.ctx (by decide) hc₀
  exact addL hc₀.ok a3 a4 (hc.sep00 (by kdecide) (by kdecide) (by kdecide)) hc.cw (mem_rd_wr hc.cw)
    r.acc r.tmp (hc.alP _) (hc.alP _) fun s₄ k₄ p₄ => ⟨r.kx.trans ((k₄.x _).subL hc₀ (by kdecide)),
      by rw [k₄.cs .s5 (by decide), r.s5], p₄⟩

omit hc₀ ha hv h in
theorem dot5_ok {s₄ : State} (r : DC K L a v s₀ j s₄) :
    WP isa (.block (count .s5 K.k)) s₄ fun s' =>
      DotInv K L a v s₀ (j + 1) s' ∧ (s'.gpr .t0 != 0) = decide (j + 1 ≠ K.k) := by
  have k4 := hK.k4
  exact WP.mono (count_ok (by decide) (by omega) (by omega) r.s5) fun s' ⟨k', g', z'⟩ =>
    ⟨⟨r.kx.trans (k'.mono (fun _ h => absurd h List.not_mem_nil)), g',
      polyIs_frame k'.frame (fun _ h => absurd h List.not_mem_nil) r.acc⟩, z'⟩

end
theorem dotBody_ok {K : KemLay} (hK : K.WF) {L : Lay} {a v : Nat → Poly} {s₀ : State} (hc₀ : Ctx L s₀)
    (ha : ∀ j < K.k, PolyIs s₀.mem (L.A 0 (oPoly j)) (a j))
    (hv : ∀ j < K.k, PolyIs s₀.mem (L.A 0 (oPoly (K.k + j))) (v j))
    {j : Nat} (hj : j < K.k) {s : State} (h : DotInv K L a v s₀ j s) :
    WP isa K.dotBody s fun s' => DotInv K L a v s₀ (j + 1) s' ∧ (s'.gpr .t0 != 0) = decide (j + 1 ≠ K.k) :=
  WP.seq (WP.mono (dot1_ok hK hc₀ hj h) fun _ ⟨o₁, m3, m4, m5, m6⟩ =>
    WP.seq (WP.mono (dot2_ok hK hc₀ ha hv hj h o₁ m3 m4 m5 m6) fun _ r₂ =>
    WP.seq (WP.mono (dot3_ok hK hc₀ r₂) fun _ ⟨r₃, a3, a4⟩ =>
    WP.seq (WP.mono (dot4_ok hK hc₀ r₃ a3 a4) fun _ r₄ => dot5_ok hK hj r₄))))

theorem dot_ok {K : KemLay} (hK : K.WF) {L : Lay} {a v : Nat → Poly} {s₀ : State} (hc₀ : Ctx L s₀)
    (ha : ∀ j < K.k, PolyIs s₀.mem (L.A 0 (oPoly j)) (a j))
    (hv : ∀ j < K.k, PolyIs s₀.mem (L.A 0 (oPoly (K.k + j))) (v j)) :
    WP isa K.dot s₀ fun s => KeptX [.s5] (L.RL (dotW K)) s₀ s ∧
      PolyIs s.mem (L.A 0 K.oAcc) (VG.Proof.MlKem.KPke.dotK a v K.k) := by
  refine WP.seq (WP.mono (zeroPoly_ok hc₀ (by offs)) fun s₁ ⟨k₁, z₁⟩ => ?_)
  refine WP.seq (WP.mono (li_ok .s5 (N := 0) (by decide)) fun s₂ ⟨k₂, g₂, m₂⟩ => ?_)
  refine wp_loop_nz (DotInv K L a v s₀) (N := K.k) (by have := hK.k1; omega)
    (fun j hj s h => dotBody_ok hK hc₀ ha hv hj h)
    (fun _ h => ⟨h.kx, by rw [← rowAcc_eq]; exact h.acc⟩)
    ⟨((k₁.x _).subL hc₀ (by kdecide)).trans (k₂.mono (fun _ h => absurd h List.not_mem_nil)), g₂,
      by rw [m₂]; exact z₁⟩

end VG.Proof.MlKem.RISCV64

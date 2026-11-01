module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Pack.Encode
public import VerifiedGarbage.Proof.MlDsa.Pack.Mem
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.Stream
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Sha3.PPC64LE.Stream

/-!
# ML-DSA on PPC64LE: the contracts of the encodings, for the proofs

For each function of this group, what its shared contract
(`Proof/MlDsa/Contract.lean`) requires, spelled out for PPC64LE (`SbpPre`, `BpPre`,
`BuPre`, `T1Pre`, from `pre_of`). A `u32` argument is the low 32 bits of its
register (`lo`): the ABI leaves the others unspecified, and the contracts
make only those public. So the branch of `sel` on a width compares the low
32 bits (`sel_ok`), and is constant time from states that agree on them
(`sel_ct`), a fact the taint analysis, which tracks whole registers, cannot
see; the loops it chooses between are constant time by the taint analysis
(`leaf_ct`). `abi_of` derives what the calling convention preserves from the
instructions alone.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Pack

open VG VG.PPC64LE VG.Impl.MlDsa.PPC64LE.Pack
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Pack

/-- The `u32` argument in register `r`: its low 32 bits. -/
abbrev lo (s : State) (r : Reg) : Nat := ((s.gpr r).setWidth 32).toNat

/-! ## The preconditions -/

/-- `vg_mldsa_simple_bit_pack(f = r3, b = r4, out = r5, len = r6)`. -/
structure SbpPre (s : State) : Prop where
  rd : s.rd = [polyRegion (s.gpr .r3)]
  wr : s.wr = [⟨s.gpr .r5, (s.gpr .r6).toNat⟩]
  disj : (polyRegion (s.gpr .r3)).Disjoint ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
  fitF : (s.gpr .r3).toNat + 1024 ≤ 2 ^ 64
  fitO : (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64
  b : lo s .r4 ∈ simpleBitPackBounds
  len : (s.gpr .r6).toNat = 32 * bitlen (lo s .r4)
  le : ∀ i < n, (coeffAt s.mem (s.gpr .r3) i).toNat ≤ lo s .r4

theorem SbpPre.of {s : State} (h : (simpleBitPackContract PPC64LE.abi).pre s) : SbpPre s := by
  sig_pre [simpleBitPackContract, simpleBitPackSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- `vg_mldsa_bit_pack(f = r3, a = r4, b = r5, out = r6, len = r7)`. -/
structure BpPre (s : State) : Prop where
  rd : s.rd = [polyRegion (s.gpr .r3)]
  wr : s.wr = [⟨s.gpr .r6, (s.gpr .r7).toNat⟩]
  disj : (polyRegion (s.gpr .r3)).Disjoint ⟨s.gpr .r6, (s.gpr .r7).toNat⟩
  fitF : (s.gpr .r3).toNat + 1024 ≤ 2 ^ 64
  fitO : (s.gpr .r6).toNat + (s.gpr .r7).toNat ≤ 2 ^ 64
  ab : (lo s .r4, lo s .r5) ∈ bitPackParams
  len : (s.gpr .r7).toNat = 32 * bitlen (lo s .r4 + lo s .r5)
  red : Reduced s.mem (s.gpr .r3)
  bnd : ∀ i < n, -(lo s .r4 : Int) ≤ modPm (coeffAt s.mem (s.gpr .r3) i).toNat q ∧
    modPm (coeffAt s.mem (s.gpr .r3) i).toNat q ≤ lo s .r5

theorem BpPre.of {s : State} (h : (bitPackContract PPC64LE.abi).pre s) : BpPre s := by
  sig_pre [bitPackContract, bitPackSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- `vg_mldsa_bit_unpack(v = r3, len = r4, a = r5, b = r6, f = r7)`. -/
structure BuPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r3, (s.gpr .r4).toNat⟩]
  wr : s.wr = [polyRegion (s.gpr .r7)]
  disj : Region.Disjoint ⟨s.gpr .r3, (s.gpr .r4).toNat⟩ (polyRegion (s.gpr .r7))
  fitV : (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64
  fitP : (s.gpr .r7).toNat + 1024 ≤ 2 ^ 64
  ab : (lo s .r5, lo s .r6) ∈ bitPackParams
  len : (s.gpr .r4).toNat = 32 * bitlen (lo s .r5 + lo s .r6)

theorem BuPre.of {s : State} (h : (bitUnpackContract PPC64LE.abi).pre s) : BuPre s := by
  sig_pre [bitUnpackContract, bitUnpackSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- `vg_mldsa_unpack_t1(v = r3, f = r4)`. -/
structure T1Pre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r3, 320⟩]
  wr : s.wr = [polyRegion (s.gpr .r4)]
  disj : Region.Disjoint ⟨s.gpr .r3, 320⟩ (polyRegion (s.gpr .r4))
  fitV : (s.gpr .r3).toNat + 320 ≤ 2 ^ 64
  fitP : (s.gpr .r4).toNat + 1024 ≤ 2 ^ 64

theorem T1Pre.of {s : State} (h : (unpackT1Contract PPC64LE.abi).pre s) : T1Pre s := by
  sig_pre [unpackT1Contract, unpackT1Sig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem mem_bitPackParams {a b : Nat} (h : (a, b) ∈ bitPackParams) :
    (a = 2 ∧ b = 2) ∨ (a = 4 ∧ b = 4) ∨ (a = 4095 ∧ b = 4096) ∨ (a = 131071 ∧ b = 131072) ∨
      (a = 524287 ∧ b = 524288) := by
  simp only [bitPackParams, d, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  exact h

/-! ## Constants -/

/-- The value `loadB r B` leaves in `r`. -/
def loadBVal (B : Nat) : BitVec 64 :=
  if B < 2 ^ 15 then BitVec.ofNat 64 B else ((BitVec.ofNat 16 (B / 2 ^ 16)) ++ (0 : BitVec 16)).signExtend 64

theorem loadB_ok (r : Reg) {B : Nat} (hB : loadBVal B = BitVec.ofNat 64 B) (s : State) :
    WP isa (.block (loadB r B)) s fun s' =>
      (s'.gpr r = BitVec.ofNat 64 B ∧ s'.mem = s.mem) ∧ Keep [r] s s' := by
  unfold loadB
  by_cases h : B < 2 ^ 15
  · simp only [h, ↓reduceIte]
    refine WP.keep _ ?_ (by simp [writesOnly, Code.allInstrs, dstOf]) rfl
    exact wp_li h fun s₁ u₁ => wp_nil ⟨u₁.gpr, u₁.mem⟩
  · simp only [h, ↓reduceIte]
    refine WP.keep _ ?_ (by simp [writesOnly, Code.allInstrs, dstOf]) rfl
    refine WP.cons exec_lis (wp_nil ⟨?_, rfl⟩)
    rw [← hB]
    simp [loadBVal, h, State.write]

/-- The pointers of the loops from the arguments `a` and `b`. -/
theorem mov2_ok {a b : Reg} (ha : a ≠ .r0) (hb : b ≠ .r0) (hb10 : b ≠ .r10) (s : State) :
    WP isa (.block [VG.Impl.Sha3.PPC64LE.Stream.mov .r10 a, VG.Impl.Sha3.PPC64LE.Stream.mov .r11 b]) s
      fun s' => (s'.gpr .r10 = s.gpr a ∧ s'.gpr .r11 = s.gpr b ∧ s'.mem = s.mem) ∧ Keep [.r10, .r11] s s' := by
  refine WP.keep _ ?_ rfl rfl
  refine wp_addi ha (by decide) fun s₁ u₁ => wp_addi hb (by decide) fun s₂ u₂ => wp_nil ⟨?_, ?_, ?_⟩
  · rw [u₂.other _ (by decide), u₁.gpr]; exact BitVec.add_zero _
  · rw [u₂.gpr, u₁.other _ hb10]; exact BitVec.add_zero _
  · rw [u₂.mem, u₁.mem]

/-- As `mov2_ok`, then `q` in `r7`. -/
theorem mov2Q_ok {a b : Reg} (ha : a ≠ .r0) (hb : b ≠ .r0) (hb10 : b ≠ .r10) (s : State) :
    WP isa (.block ([VG.Impl.Sha3.PPC64LE.Stream.mov .r10 a, VG.Impl.Sha3.PPC64LE.Stream.mov .r11 b] ++ loadQ)) s
      fun s' => (s'.gpr .r10 = s.gpr a ∧ s'.gpr .r11 = s.gpr b ∧ s'.gpr .r7 = BitVec.ofNat 64 q ∧
        s'.mem = s.mem) ∧ Keep [.r10, .r11, .r7] s s' := by
  rw [WP.block_append_iff]
  refine WP.mono (mov2_ok ha hb hb10 s) fun s₁ ⟨⟨g10, g11, m₁⟩, k₁⟩ => ?_
  unfold loadQ
  refine wp_lis fun s₂ u₂ => wp_ori fun s₃ u₃ => wp_nil ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), g10]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), g11]
  · rw [u₃.gpr, u₂.gpr]; decide
  · rw [u₃.mem, u₂.mem, m₁]
  · exact ((k₁.trans (upd_keep u₂)).trans (upd_keep u₃)).mono (by decide)

/-! ## Branching on a width -/

/-- What the block of `sel` keeps. -/
def Same (s s' : State) : Prop := Keep [.r9] s s' ∧ s'.mem = s.mem

theorem Same.trans {a b c : State} (h₁ : Same a b) (h₂ : Same b c) : Same a c :=
  ⟨(h₁.1.trans h₂.1).mono (by decide), h₂.2.trans h₁.2⟩

theorem lo_sub_beq (x : BitVec 64) {v : Nat} (hv : v < 2 ^ 32) :
    ((x - BitVec.ofNat 64 v).setWidth 32 == 0) = decide ((x.setWidth 32).toNat = v) := by
  have e : (BitVec.ofNat 64 v).setWidth 32 = BitVec.ofNat 32 v := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : v < 2 ^ 64)]
  rw [lo32_sub, e]
  generalize x.setWidth 32 = a
  by_cases h : a.toNat = v
  · have : a = BitVec.ofNat 32 v :=
      BitVec.eq_of_toNat_eq (by rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv])
    rw [decide_eq_true h, this, BitVec.sub_self]
    rfl
  · have : a - BitVec.ofNat 32 v ≠ 0 := by
      intro e'
      apply h
      bv_omega
    rw [decide_eq_false h]
    exact beq_eq_false_iff_ne.mpr this

theorem eval_zero_w (s : State) (r : Reg) : isa.eval (.zero .w r) s = some ((s.gpr r).setWidth 32 == 0) := by
  change VG.PPC64LE.eval (.zero .w r) s = _
  simp [VG.PPC64LE.eval, State.read, Size.bits]

/-- The block of `sel`: `r9` = `r - v`. -/
theorem selBlk_ok (r : Reg) (hr : r ≠ .r9) {v : Nat} (hl : loadBVal v = BitVec.ofNat 64 v) (s : State) :
    WP isa (.block (loadB .r9 v ++ ([.sub .r9 r .r9] : List Instr))) s fun s' =>
      s'.gpr .r9 = s.gpr r - BitVec.ofNat 64 v ∧ Same s s' := by
  rw [WP.block_append_iff]
  refine WP.mono (loadB_ok .r9 hl s) fun s₁ ⟨⟨g₁, m₁⟩, k₁⟩ => wp_sub fun s₂ u₂ => wp_nil ⟨?_, ?_, ?_⟩
  · rw [u₂.gpr, g₁, k₁.gpr (by simpa using hr)]
  · exact (k₁.trans (upd_keep u₂)).mono (by decide)
  · rw [u₂.mem, m₁]

theorem sel_ok (r : Reg) (hr : r ≠ .r9) (v : Nat) (hv : v < 2 ^ 32) (hl : loadBVal v = BitVec.ofNat 64 v)
    (p e : Prog isa) (s : State) {Q : State → Prop}
    (hp : ∀ s', Same s s' → lo s r = v → WP isa p s' Q)
    (hn : ∀ s', Same s s' → lo s r ≠ v → WP isa e s' Q) :
    WP isa (sel r v p e) s Q := by
  unfold sel
  refine WP.seq (WP.mono (selBlk_ok r hr hl s) fun s' ⟨g, hs⟩ => ?_)
  refine WP.ite (M := isa) (decide (lo s r = v)) (by rw [eval_zero_w, g, lo_sub_beq _ hv])
    (fun h => hp s' hs (of_decide_eq_true h)) (fun h => hn s' hs (of_decide_eq_false h))

/-! ## Constant time -/

/-- An instruction that accesses no memory. -/
def noMem : Instr → Bool
  | .load .. | .store .. | .lbz .. | .stb .. | .loadRev .. | .storeRev .. | .push _ | .pop _
  | .alloc _ | .lxvd2x .. | .lxvd2xTbl .. | .stxvd2x .. => false
  | _ => true

theorem addrs_noMem {i : Instr} (h : noMem i = true) (s : State) : VG.PPC64LE.addrs i s = [] := by
  cases i <;> first | rfl | simp [noMem] at h

theorem execBlock_noMem : ∀ {is : List Instr}, is.all noMem = true → ∀ {s s' : State} {t : List Leak},
    execBlock isa is s = some (s', t) → t = []
  | [], _, _, _, _, h => by simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
  | i :: is, hm, s, s', t, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hm
    simp only [execBlock] at h
    split at h
    · cases h
    · obtain ⟨⟨s'', t'⟩, h₁, h₂⟩ := Option.map_eq_some_iff.mp h
      cases h₂
      rw [addrs_noMem hm.1 s]
      simpa using execBlock_noMem hm.2 h₁

/-- A block that accesses no memory leaks nothing. -/
theorem relct_noMem {P : State → State → Prop} {is : List Instr} (h : is.all noMem = true) :
    RelCT isa P (.block is) fun _ _ => True := fun _ _ _ _ _ _ _ e₁ e₂ => by
  rw [Exec.block_iff] at e₁ e₂
  rw [execBlock_noMem h e₁, execBlock_noMem h e₂]; exact ⟨rfl, trivial⟩

theorem WP.withSp {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.sp = s.sp :=
  let ⟨t, s', he, hq⟩ := h
  ⟨t, s', he, hq, Exec.sp he⟩

/-- Two runs that agree on the stack pointer, the pointers of the loops and
the `u32` argument in `r`. -/
def Agr (r : Reg) (a b : State) : Prop :=
  a.sp = b.sp ∧ a.gpr .r10 = b.gpr .r10 ∧ a.gpr .r11 = b.gpr .r11 ∧ lo a r = lo b r

theorem sel_ct {r : Reg} (hr : r ≠ .r9) {v : Nat} (hl : loadBVal v = BitVec.ofNat 64 v)
    {p e : Prog isa} {Q : State → State → Prop} (hp : RelCT isa (Agr r) p Q) (he : RelCT isa (Agr r) e Q) :
    RelCT isa (Agr r) (sel r v p e) Q := by
  unfold sel
  have hb := (relct_noMem (P := Agr r) (is := loadB .r9 v ++ ([.sub .r9 r .r9] : List Instr))
    (by unfold loadB; split <;> rfl)).wpDep
    (F := fun (σ s' : State) => (s'.gpr .r9 = σ.gpr r - BitVec.ofNat 64 v ∧ Same σ s') ∧ s'.sp = σ.sp)
    fun a b _ => ⟨WP.withSp (selBlk_ok r hr hl a), WP.withSp (selBlk_ok r hr hl b)⟩
  refine RelCT.seq (R := fun a b => Agr r a b ∧ isa.eval (.zero .w .r9) a = isa.eval (.zero .w .r9) b)
    (hb.mono (fun _ _ h => h) fun a' b' ⟨_, σ₁, σ₂, hσ, ⟨⟨g₁, k₁, _⟩, p₁⟩, ⟨⟨g₂, k₂, _⟩, p₂⟩⟩ =>
      ⟨⟨by rw [p₁, p₂, hσ.1], by rw [k₁.gpr (by decide), k₂.gpr (by decide), hσ.2.1],
        by rw [k₁.gpr (by decide), k₂.gpr (by decide), hσ.2.2.1],
        by simp only [lo]; rw [k₁.gpr (by simpa using hr), k₂.gpr (by simpa using hr)]; exact hσ.2.2.2⟩,
      by
        rw [eval_zero_w, eval_zero_w, g₁, g₂, lo32_sub, lo32_sub]
        have : (σ₁.gpr r).setWidth 32 = (σ₂.gpr r).setWidth 32 := BitVec.eq_of_toNat_eq hσ.2.2.2
        rw [this]⟩)
    (RelCT.ite (fun _ _ h => h.2) (hp.mono (fun _ _ h => h.1.1) fun _ _ h => h)
      (he.mono (fun _ _ h => h.1.1) fun _ _ h => h))

/-- A branch of `sel`, constant time by the taint analysis with the pointers
of the loops public. -/
theorem leaf_ct {r : Reg} {c : Prog isa} {hc : VG.Taint.Hint VG.PPC64LE.taint.T}
    (h : (VG.PPC64LE.taint.check (Taint.ofRegs [.r10, .r11]) c hc).isSome = true) :
    RelCT isa (Agr r) c fun _ _ => True :=
  RelCT.taint (A := VG.PPC64LE.taint) (Taint.ofRegs [.r10, .r11]) (fun a b h => ⟨h.1, fun x hx => by
    rw [Taint.mem_ofRegs] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    exacts [h.2.1, h.2.2.1]⟩) h

/-! ## The calling convention -/

/-- Code without calls that writes no register the calling convention
preserves, nor the link register, preserves what it must. -/
theorem abi_of {c : Prog isa}
    (hp : (instrs c).all (fun i => preserved.all fun r => dstOf i != some r) = true) (hn : c.noCalls = true)
    (hl : (instrs c).all (fun i => !i.writesLr) = true) {s s' : State} {t : List Leak}
    (he : Exec isa c s t s') : abiPreserved s s' := by
  refine ⟨fun r hr => Exec.gpr (fun i hi h => ?_) he (.inl hn), Exec.sp he, Exec.lr he hn hl⟩
  have := List.all_eq_true.mp (List.all_eq_true.mp hp i hi) r hr
  rw [h] at this
  simp at this

end VG.Proof.MlDsa.PPC64LE.Pack

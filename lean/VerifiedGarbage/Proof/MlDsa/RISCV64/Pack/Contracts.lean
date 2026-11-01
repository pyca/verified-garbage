module

public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Pack.Encode
public import VerifiedGarbage.Proof.MlDsa.Pack.Mem
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.Stream
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Common

/-!
# ML-DSA on RISC-V: the contracts of the encodings, for the proofs

For each function of this group, what its shared contract
(`Spec/MlDsa/Poly.lean`) requires, spelled out for RISCV64 (`SbpPre`, `BpPre`,
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

namespace VG.Proof.MlDsa.RISCV64.Pack

open VG VG.RISCV64 VG.Impl.MlDsa.RISCV64.Pack
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Pack

/-- The `u32` argument in register `r`: its low 32 bits. -/
abbrev lo (s : State) (r : Reg) : Nat := ((s.gpr r).setWidth 32).toNat

/-! ## The preconditions -/

/-- `vg_mldsa_simple_bit_pack(f = a0, b = a1, out = a2, len = a3)`. -/
structure SbpPre (s : State) : Prop where
  rd : s.rd = [polyRegion (s.gpr .a0)]
  wr : s.wr = [⟨s.gpr .a2, (s.gpr .a3).toNat⟩]
  disj : (polyRegion (s.gpr .a0)).Disjoint ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
  fitF : (s.gpr .a0).toNat + 1024 ≤ 2 ^ 64
  fitO : (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64
  b : lo s .a1 ∈ simpleBitPackBounds
  len : (s.gpr .a3).toNat = 32 * bitlen (lo s .a1)
  le : ∀ i < n, (coeffAt s.mem (s.gpr .a0) i).toNat ≤ lo s .a1
  al : (s.gpr .a0).toNat % 4 = 0

theorem SbpPre.of {s : State} (h : (simpleBitPackContract RISCV64.abi).pre s) : SbpPre s := by
  sig_pre [simpleBitPackContract, simpleBitPackSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- `vg_mldsa_bit_pack(f = a0, a = a1, b = a2, out = a3, len = a4)`. -/
structure BpPre (s : State) : Prop where
  rd : s.rd = [polyRegion (s.gpr .a0)]
  wr : s.wr = [⟨s.gpr .a3, (s.gpr .a4).toNat⟩]
  disj : (polyRegion (s.gpr .a0)).Disjoint ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
  fitF : (s.gpr .a0).toNat + 1024 ≤ 2 ^ 64
  fitO : (s.gpr .a3).toNat + (s.gpr .a4).toNat ≤ 2 ^ 64
  ab : (lo s .a1, lo s .a2) ∈ bitPackParams
  len : (s.gpr .a4).toNat = 32 * bitlen (lo s .a1 + lo s .a2)
  red : Reduced s.mem (s.gpr .a0)
  bnd : ∀ i < n, -(lo s .a1 : Int) ≤ modPm (coeffAt s.mem (s.gpr .a0) i).toNat q ∧
    modPm (coeffAt s.mem (s.gpr .a0) i).toNat q ≤ lo s .a2
  al : (s.gpr .a0).toNat % 4 = 0

theorem BpPre.of {s : State} (h : (bitPackContract RISCV64.abi).pre s) : BpPre s := by
  sig_pre [bitPackContract, bitPackSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-- `vg_mldsa_bit_unpack(v = a0, len = a1, a = a2, b = a3, f = a4)`. -/
structure BuPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a0, (s.gpr .a1).toNat⟩]
  wr : s.wr = [polyRegion (s.gpr .a4)]
  disj : Region.Disjoint ⟨s.gpr .a0, (s.gpr .a1).toNat⟩ (polyRegion (s.gpr .a4))
  fitV : (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64
  fitP : (s.gpr .a4).toNat + 1024 ≤ 2 ^ 64
  ab : (lo s .a2, lo s .a3) ∈ bitPackParams
  len : (s.gpr .a1).toNat = 32 * bitlen (lo s .a2 + lo s .a3)
  al : (s.gpr .a4).toNat % 4 = 0

theorem BuPre.of {s : State} (h : (bitUnpackContract RISCV64.abi).pre s) : BuPre s := by
  sig_pre [bitUnpackContract, bitUnpackSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- `vg_mldsa_unpack_t1(v = a0, f = a1)`. -/
structure T1Pre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a0, 320⟩]
  wr : s.wr = [polyRegion (s.gpr .a1)]
  disj : Region.Disjoint ⟨s.gpr .a0, 320⟩ (polyRegion (s.gpr .a1))
  fitV : (s.gpr .a0).toNat + 320 ≤ 2 ^ 64
  fitP : (s.gpr .a1).toNat + 1024 ≤ 2 ^ 64
  al : (s.gpr .a1).toNat % 4 = 0

theorem T1Pre.of {s : State} (h : (unpackT1Contract RISCV64.abi).pre s) : T1Pre s := by
  sig_pre [unpackT1Contract, unpackT1Sig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem mem_bitPackParams {a b : Nat} (h : (a, b) ∈ bitPackParams) :
    (a = 2 ∧ b = 2) ∨ (a = 4 ∧ b = 4) ∨ (a = 4095 ∧ b = 4096) ∨ (a = 131071 ∧ b = 131072) ∨
      (a = 524287 ∧ b = 524288) := by
  simp only [bitPackParams, d, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  exact h

/-! ## Constants -/

/-- The value `loadB r B` leaves in `r`, when `B` is small enough for it. -/
def loadBVal (B : Nat) : BitVec 64 :=
  if B < 2 ^ 31 - 2048 then BitVec.ofNat 64 B else BitVec.ofNat 64 B + 1

theorem loadB_ok (r : Reg) {B : Nat} (hB : loadBVal B = BitVec.ofNat 64 B) (s : State) :
    WP isa (.block (loadB r B)) s fun s' =>
      (s'.gpr r = BitVec.ofNat 64 B ∧ s'.mem = s.mem) ∧ Keep [r] s s' := by
  by_cases h : B < 2 ^ 31 - 2048
  · unfold loadB VG.Impl.MlDsa.RISCV64.Arith.loadImm
    refine WP.keep _ ?_ (by simp [writesOnly, Code.allInstrs, dstOf]) rfl
    refine Steps.WP.cons exec_lui (Steps.WP.cons (exec_addi (VG.Proof.MlDsa.RISCV64.Arith.loadImm_imm _))
      (WP.block_nil ⟨?_, rfl⟩))
    simp only [State.write, ite_true]
    exact VG.Proof.MlDsa.RISCV64.Arith.loadImm_val h
  · exact absurd hB (by simp [loadBVal, h])

/-- The pointers of the loops from the arguments `a` and `b`. -/
theorem mov2_ok {a b : Reg} (hb10 : b ≠ .a7) (s : State) :
    WP isa (.block [.addi .a7 a 0, .addi .t1 b 0]) s
      fun s' => (s'.gpr .a7 = s.gpr a ∧ s'.gpr .t1 = s.gpr b ∧ s'.mem = s.mem) ∧ Keep [.a7, .t1] s s' := by
  refine WP.keep _ ?_ rfl rfl
  refine Steps.wp_mv fun s₁ u₁ => Steps.wp_mv fun s₂ u₂ => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [u₂.other _ (by decide), u₁.gpr]
  · rw [u₂.gpr, u₁.other _ hb10]
  · rw [u₂.mem, u₁.mem]

/-- As `mov2_ok`, then `q` in `a4`. -/
theorem mov2Q_ok {a b : Reg} (hb10 : b ≠ .a7) (s : State) :
    WP isa (.block ([.addi .a7 a 0, .addi .t1 b 0] ++ loadQ)) s
      fun s' => (s'.gpr .a7 = s.gpr a ∧ s'.gpr .t1 = s.gpr b ∧ s'.gpr .a4 = BitVec.ofNat 64 q ∧
        s'.mem = s.mem) ∧ Keep [.a7, .t1, .a4] s s' := by
  rw [WP.block_append_iff]
  refine WP.mono (mov2_ok hb10 s) fun s₁ ⟨⟨g10, g11, m₁⟩, k₁⟩ => ?_
  simp only [loadQ, VG.Proof.MlDsa.RISCV64.Arith.loadImm_q]
  refine Steps.WP.cons exec_lui (Steps.WP.cons (exec_addi (by decide)) (WP.block_nil ⟨⟨?_, ?_, ?_, m₁⟩, ?_⟩))
  · simp only [State.write, reduceCtorEq, ite_false]; exact g10
  · simp only [State.write, reduceCtorEq, ite_false]; exact g11
  · simp only [State.write, ite_true]; decide
  · exact ((k₁.trans (upd_keep (Steps.Upd.write _ _ _))).trans (upd_keep (Steps.Upd.write _ _ _))).mono
      (by decide)

/-! ## Branching on a width -/

/-- What the block of `sel` keeps. -/
def Same (s s' : State) : Prop := Keep [.a6] s s' ∧ s'.mem = s.mem

theorem Same.trans {a b c : State} (h₁ : Same a b) (h₂ : Same b c) : Same a c :=
  ⟨(h₁.1.trans h₂.1).mono (by decide), h₂.2.trans h₁.2⟩

/-- What `subw` of `x` and `v` leaves. -/
def subwV (x : BitVec 64) (v : Nat) : BitVec 64 := sext32 (x.setWidth 32 - (BitVec.ofNat 64 v).setWidth 32)

theorem lo_sub_beq (x : BitVec 64) {v : Nat} (hv : v < 2 ^ 32) :
    (subwV x v == 0) = decide ((x.setWidth 32).toNat = v) := by
  have e : (BitVec.ofNat 64 v).setWidth 32 = BitVec.ofNat 32 v := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : v < 2 ^ 64)]
  rw [subwV, VG.Proof.MlDsa.RISCV64.Arith.sext32_beq_zero, e]
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

theorem eval_zero (s : State) (r : Reg) : isa.eval (.zero r) s = some (s.gpr r == 0) := rfl

/-- The block of `sel`: `a6` = `r - v` on the low halves. -/
theorem selBlk_ok (r : Reg) (hr : r ≠ .a6) {v : Nat} (hl : loadBVal v = BitVec.ofNat 64 v) (s : State) :
    WP isa (.block (loadB .a6 v ++ ([.subw .a6 r .a6] : List Instr))) s fun s' =>
      s'.gpr .a6 = subwV (s.gpr r) v ∧ Same s s' := by
  rw [WP.block_append_iff]
  refine WP.mono (loadB_ok .a6 hl s) fun s₁ ⟨⟨g₁, m₁⟩, k₁⟩ =>
    Steps.WP.cons exec_subw (WP.block_nil ⟨?_, ?_, ?_⟩)
  · simp only [State.write, ite_true, subwV]; rw [g₁, k₁.gpr (by simpa using hr)]
  · exact (k₁.trans (upd_keep (Steps.Upd.write _ _ _))).mono (by decide)
  · exact m₁

theorem sel_ok (r : Reg) (hr : r ≠ .a6) (v : Nat) (hv : v < 2 ^ 32) (hl : loadBVal v = BitVec.ofNat 64 v)
    (p e : Prog isa) (s : State) {Q : State → Prop}
    (hp : ∀ s', Same s s' → lo s r = v → WP isa p s' Q)
    (hn : ∀ s', Same s s' → lo s r ≠ v → WP isa e s' Q) :
    WP isa (sel r v p e) s Q := by
  unfold sel
  refine WP.seq (WP.mono (selBlk_ok r hr hl s) fun s' ⟨g, hs⟩ => ?_)
  refine WP.ite (M := isa) (decide (lo s r = v)) (by rw [eval_zero, g, lo_sub_beq _ hv])
    (fun h => hp s' hs (of_decide_eq_true h)) (fun h => hn s' hs (of_decide_eq_false h))

/-! ## Constant time -/

/-- An instruction that accesses no memory. -/
def noMem : Instr → Bool
  | .load .. | .store .. | .push _ | .pop _ => false
  | _ => true

theorem addrs_noMem {i : Instr} (h : noMem i = true) (s : State) : VG.RISCV64.addrs i s = [] := by
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
  a.sp = b.sp ∧ a.gpr .a7 = b.gpr .a7 ∧ a.gpr .t1 = b.gpr .t1 ∧ lo a r = lo b r

theorem sel_ct {r : Reg} (hr : r ≠ .a6) {v : Nat} (hl : loadBVal v = BitVec.ofNat 64 v)
    {p e : Prog isa} {Q : State → State → Prop} (hp : RelCT isa (Agr r) p Q) (he : RelCT isa (Agr r) e Q) :
    RelCT isa (Agr r) (sel r v p e) Q := by
  unfold sel
  have hb := (relct_noMem (P := Agr r) (is := loadB .a6 v ++ ([.subw .a6 r .a6] : List Instr))
    (by unfold loadB VG.Impl.MlDsa.RISCV64.Arith.loadImm; rfl)).wpDep
    (F := fun (σ s' : State) => (s'.gpr .a6 = subwV (σ.gpr r) v ∧ Same σ s') ∧ s'.sp = σ.sp)
    fun a b _ => ⟨WP.withSp (selBlk_ok r hr hl a), WP.withSp (selBlk_ok r hr hl b)⟩
  refine RelCT.seq (R := fun a b => Agr r a b ∧ isa.eval (.zero .a6) a = isa.eval (.zero .a6) b)
    (hb.mono (fun _ _ h => h) fun a' b' ⟨_, σ₁, σ₂, hσ, ⟨⟨g₁, k₁, _⟩, p₁⟩, ⟨⟨g₂, k₂, _⟩, p₂⟩⟩ =>
      ⟨⟨by rw [p₁, p₂, hσ.1], by rw [k₁.gpr (by decide), k₂.gpr (by decide), hσ.2.1],
        by rw [k₁.gpr (by decide), k₂.gpr (by decide), hσ.2.2.1],
        by simp only [lo]; rw [k₁.gpr (by simpa using hr), k₂.gpr (by simpa using hr)]; exact hσ.2.2.2⟩,
      by
        rw [eval_zero, eval_zero, g₁, g₂, subwV, subwV]
        have : (σ₁.gpr r).setWidth 32 = (σ₂.gpr r).setWidth 32 := BitVec.eq_of_toNat_eq hσ.2.2.2
        rw [this]⟩)
    (RelCT.ite (fun _ _ h => h.2) (hp.mono (fun _ _ h => h.1.1) fun _ _ h => h)
      (he.mono (fun _ _ h => h.1.1) fun _ _ h => h))

/-- A branch of `sel`, constant time by the taint analysis with the pointers
of the loops public. -/
theorem leaf_ct {r : Reg} {c : Prog isa} {hc : VG.Taint.Hint VG.RISCV64.taint.T}
    (h : (VG.RISCV64.taint.check (Taint.ofRegs [.a7, .t1]) c hc).isSome = true) :
    RelCT isa (Agr r) c fun _ _ => True :=
  RelCT.taint (A := VG.RISCV64.taint) (Taint.ofRegs [.a7, .t1]) (fun a b h => ⟨h.1, fun x hx => by
    rw [Taint.mem_ofRegs] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    exacts [h.2.1, h.2.2.1]⟩) h

/-! ## The calling convention -/

/-- Code without calls that writes neither a register the calling convention
preserves nor the return address preserves what it must. -/
theorem abi_of {c : Prog isa}
    (hp : (instrs c).all (fun i => (Reg.ra :: preserved).all fun r => dstOf i != some r) = true)
    (hn : callFree c = true) {s s' : State} {t : List Leak}
    (he : Exec isa c s t s') : abiPreserved s s' := by
  have hw : ∀ r ∈ Reg.ra :: preserved, ∀ i ∈ instrs c, dstOf i ≠ some r := fun r hr i hi h => by
    have := List.all_eq_true.mp (List.all_eq_true.mp hp i hi) r hr
    rw [h] at this
    simp at this
  exact ⟨fun r hr => Exec.gpr_callFree (hw r (List.mem_cons_of_mem _ hr)) he hn, Exec.sp he,
    Exec.gpr_callFree (hw .ra (List.mem_cons_self ..)) he hn⟩

end VG.Proof.MlDsa.RISCV64.Pack

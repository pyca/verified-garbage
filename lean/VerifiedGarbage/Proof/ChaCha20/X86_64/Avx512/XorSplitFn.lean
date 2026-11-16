module

public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.XorSplit
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512Tail.Sym
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.SymSel
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Last
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.FinishSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Copy
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Variant
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Xor
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-! ### `ChaCha20.X86_64.Avx512.LastSel`, which only this module used -/

section

/-! ### `ChaCha20.X86_64.Avx512Tail.SymSel`, which only this module used -/

section

/-!
# ChaCha20 on x86-64 with AVX-512, the last bytes: blocks of the input from either buffer

`Avx512/SymSel.lean` for the code of the last pass, with `buf` at `r9` and
`4 D` bytes of data (`Sym.lean`): `selD` runs both branches of a `selXor`,
loading the block as `T.inp`, and `sel_ok` proves either branch agrees.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Avx512Tail

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx512
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.ChaCha20 (Word)
open VG.Proof.ChaCha20.X86_64.Avx512 (T Sym Sym.setReg zw zw_split xidx div4_lt pick4_ext dword_read512
  add_ofNat' ofInt_ofNat inpW srcR cmpR10_ok inp_block)

/-- `Avx512.Sym.sel`, in a pass of `4 D` bytes of data. -/
def selD (D : Nat) (σ : Sym) (x t : XReg) (off : Nat) : Option Sym :=
  if off % 64 = 0 ∧ off / 4 + 16 ≤ D ∧
      (List.range 16).all (fun p => σ.mem 2 (off / 4 + p) == .mem 2 (off / 4 + p)) then
    run D (σ.setReg (xidx t) fun p => .inp (off / 4 + p)) [z .vpxord t t x, .vmovdqu32Store (at_ .rsi off) t]
  else none

def runPieces (D : Nat) (σ : Sym) : List Piece → Option Sym
  | [] => some σ
  | .ins is :: ps => (run D σ is).bind fun σ' => runPieces D σ' ps
  | .sel x t off :: ps => (selD D σ x t off).bind fun σ' => runPieces D σ' ps

/-- The bytes of `src` the pass may load are readable, and it does not write
them. -/
structure SelOk (D : Nat) (s₀ : State) : Prop where
  r : ∀ a n, 0 < n → (srcR s₀).Contains a n → InRegions (s₀.rd ++ s₀.wr) a n
  d : ∀ r ∈ wregs D s₀, (srcR s₀).Disjoint r

theorem SRel.congr {D : Nat} {σ : Sym} {s₀ s s' : State} (h : SRel D σ s₀ s)
    (hz : ∀ r p, zw s' r p = zw s r p) (hm : s'.mem = s.mem) (hg : s'.gpr = s.gpr) (hr : s'.rd = s.rd)
    (hw : s'.wr = s.wr) : SRel D σ s₀ s' :=
  SRel.mk' (fun r p hp => (hz r p).trans (h.reg r p hp)) (fun b i hb hi => by rw [hm]; exact h.mem b i hb hi)
    (hg.trans h.gpr) (hr.trans h.rd) (hw.trans h.wr) (hm ▸ h.frame) fun hd => hm.trans (h.clean hd)

/-- A load of 64 bytes whose doublewords are given terms. -/
theorem SRel.load {D : Nat} {σ : Sym} {s₀ s : State} (h : SRel D σ s₀ s) (d : XReg) (m : MemOp) {f : Nat → T}
    (hin : InRegions (s.rd ++ s.wr) (s.ea m) 64)
    (hv : ∀ p < 16, s.mem.readW (s.ea m + BitVec.ofNat 64 (4 * p)) 32 = T.eval D s₀ (f p)) :
    ∃ s', exec (.vmovdqu32Load d m) s = some s' ∧ SRel D (σ.setReg (xidx d) f) s₀ s' := by
  refine ⟨s.setZ d ((s.mem.readW (s.ea m) 512).extractLsb' 0 128)
    ((s.mem.readW (s.ea m) 512).extractLsb' 128 128)
    ((s.mem.readW (s.ea m) 512).extractLsb' 256 128)
    ((s.mem.readW (s.ea m) 512).extractLsb' 384 128), by simp only [exec, State.load512, hin, ite_true, Option.map_some],
    h.setReg (fun r p hp => ?_) (by simp) (by simp) (by simp) (by simp)⟩
  rw [zw_split, State.zlane_setZ _ _ _ _ _ _ _ (div4_lt hp)]
  split
  · rw [pick4_ext _ (div4_lt hp), dword_read512 _ _ hp]
    exact hv p hp
  · rfl

theorem sel_ok {D : Nat} {s₀ : State} (hc : Ctx D s₀) (hs : SelOk D s₀) {σ σ' : Sym} {s : State}
    (h : SRel D σ s₀ s) {x t : XReg} {off : Nat} (e : selD D σ x t off = some σ') :
    WP isa (selXor x t off) s (SRel D σ' s₀) := by
  have hD := hc.small
  unfold selD at e
  split at e
  case isFalse => cases e
  rename_i hcond
  obtain ⟨hoff, hlim, hcl⟩ := hcond
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hcl
  refine WP.seq (WP.mono (cmpR10_ok s (c := off + 64) (by omega_using [hD, hlim])) fun s₁ ⟨g₁, m₁, rd₁, wr₁, z₁, c₁⟩ => ?_)
  obtain h₁ : SRel D σ s₀ s₁ := h.congr z₁ m₁ g₁ rd₁ wr₁
  obtain ea : ∀ r, s₁.ea (at_ r off) = s₀.gpr r + BitVec.ofNat 64 off := fun r => by
    simp only [State.ea, at_, g₁, h.gpr]
    exact congrArg _ (ofInt_ofNat off)
  obtain rest : ∀ s₂ : State, SRel D (σ.setReg (xidx t) fun p => .inp (off / 4 + p)) s₀ s₂ →
      WP isa (.block [z .vpxord t t x, .vmovdqu32Store (at_ .rsi off) t]) s₂ (SRel D σ' s₀) :=
    fun s₂ h₂ => srun_ok hc _ h₂ e
  refine WP.ite (decide ((s₀.gpr .r10).toNat < off + 64)) (by simp [eval, c₁, h.gpr]) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    obtain i2 : InRegions (s₁.rd ++ s₁.wr) ((regn D s₀ 2).base + BitVec.ofNat 64 (4 * (off / 4))) (4 * 16) :=
      in_regn' hc (b := 2) (by decide) (wr₁.trans h.wr) (by simp only [bsize]; omega_using [hlim]) (by decide)
    obtain ea2 : s₁.ea (at_ .rsi off) = (regn D s₀ 2).base + BitVec.ofNat 64 (4 * (off / 4)) := by
      rw [ea]; simp only [regn, baseR]; congr 2; omega_using [hoff]
    obtain ⟨s₂, hx, h₂⟩ := h₁.load t (at_ .rsi off) (f := fun p => .inp (off / 4 + p)) (by rw [ea2]; exact i2)
      (fun p hp => by
        rw [ea2, add_ofNat', ← Nat.mul_add, h₁.mem 2 _ (by decide) (by simp only [bsize]; omega_using [hlim, hp]), hcl p hp]
        simp only [T.eval, inpW, inp_block hoff hp, memBase_2]
        rw [ite_eq_right (by omega_using [hoff, hb])])
    exact WP.block_cons_iff.2 ⟨s₂, hx, rest s₂ h₂⟩
  · simp only [decide_eq_false_iff_not, Nat.not_lt] at hb
    obtain cs : (srcR s₀).Contains (s₀.gpr .r8 + BitVec.ofNat 64 off) 64 := by
      simp only [srcR, Region.Contains]
      rw [show s₀.gpr .r8 + BitVec.ofNat 64 off - s₀.gpr .r8 = BitVec.ofNat 64 off by bv_omega_arith,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hb])]
      omega_using [hD, hlim, hb]
    obtain ⟨s₂, hx, h₂⟩ := h₁.load t (at_ .r8 off) (f := fun p => .inp (off / 4 + p))
      (by rw [ea, rd₁, wr₁, h.rd, h.wr]; exact hs.r _ _ (by decide) cs)
      (fun p hp => by
        obtain cp : (srcR s₀).Contains (s₀.gpr .r8 + BitVec.ofNat 64 off + BitVec.ofNat 64 (4 * p)) (32 / 8) := by
          simp only [srcR, Region.Contains] at cs ⊢
          rw [show s₀.gpr .r8 + BitVec.ofNat 64 off + BitVec.ofNat 64 (4 * p) - s₀.gpr .r8 =
            BitVec.ofNat 64 (off + 4 * p) by rw [add_ofNat']; bv_omega_arith,
            BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hb, hp])]
          rw [show s₀.gpr .r8 + BitVec.ofNat 64 off - s₀.gpr .r8 = BitVec.ofNat 64 off by bv_omega_arith,
            BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hb])] at cs
          omega_using [cs, hp]
        rw [ea, m₁, h.frame.readW cp hs.d (by decide)]
        simp only [T.eval, inpW, inp_block hoff hp]
        rw [ite_eq_left (by omega_using [hb]), add_ofNat', show off + 4 * p = 4 * (off / 4 + p) by omega_using [hoff]])
    exact WP.block_cons_iff.2 ⟨s₂, hx, rest s₂ h₂⟩

/-- `pieces`. -/
theorem runPieces_ok {D : Nat} {s₀ : State} (hc : Ctx D s₀) (hs : SelOk D s₀) :
    ∀ (ps : List Piece) {σ σ' : Sym} {s : State}, SRel D σ s₀ s → runPieces D σ ps = some σ' →
      WP isa (pieces ps) s (SRel D σ' s₀)
  | [], _, _, _, h, e => by cases e; exact WP.block_nil h
  | .ins is :: ps, _, _, _, h, e => by
    simp only [runPieces, Option.bind_eq_some_iff] at e
    obtain ⟨σ₁, e₁, e₂⟩ := e
    show WP isa (.seq (.block is) (pieces ps)) _ _
    exact WP.seq (WP.mono (srun_ok hc is h e₁) fun s₁ h₁ => runPieces_ok hc hs ps h₁ e₂)
  | .sel x t off :: ps, _, _, _, h, e => by
    simp only [runPieces, Option.bind_eq_some_iff] at e
    obtain ⟨σ₁, e₁, e₂⟩ := e
    show WP isa (.seq (selXor x t off) (pieces ps)) _ _
    exact WP.seq (WP.mono (sel_ok hc hs h e₁) fun s₁ h₁ => runPieces_ok hc hs ps h₁ e₂)

end VG.Proof.ChaCha20.X86_64.Avx512Tail

end

end


/-!
# ChaCha20 keystream XOR with the data's first bytes from another buffer on x86-64 with AVX-512: the last 513 to 1023 bytes

`last16Sel`, from the state after the loop (`SInv`, with 513 to 1023 bytes
left) to the end of the function, as `last16` (`Last.lean`), each block of
the input loaded by `selXor`: the first eight by `finishPSel`, the next as
far as they fit by `condSel`, and the block the data ends in, if it ends
within one, from `dst`, where the input's bytes from `C` on are.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Avx512Split

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx512
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.ChaCha20 (Word stateAt keystream serialize)
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86_64.Avx512 (T Sym Sym.init xidx xidx_lt zw ZH Incs outT srcR inpW inpW_byte byte_dword)
open VG.Proof.ChaCha20.X86_64.Avx512Tail (Ctx SRel srun_ok regn baseR bsize wregs selD S0)
open VG.Proof.ChaCha20.X86_64.Avx512Last (outT_eval condS_run cmpJ_ok adv512_ok adv_ok mov_ok At bufR_sub)
open VG.Proof.ChaCha20.X86_64.Avx2Tail (winS winS_sub winQ winQ_sub not_winQ)
open VG.Proof.ChaCha20.X86_64.Avx2 (add_ofNat plus)

/-! ## The kernel's checks -/

def finishPSelCheck : Bool :=
  match Avx512Tail.runPieces 128 Sym.init finishPSel with
  | some σ =>
    ((List.range 128).all fun i => σ.mem 2 i == .xor (.inp i) (outT (i % 16) (i / 16))) &&
    (List.range 8).all fun j => (List.range 16).all fun p =>
      σ.reg (xidx (blkReg (8 + j))) p == outT p (8 + j)
  | none => false

/-- The block register into the data, by `selXor`, for each `j`, and the
other block registers kept. -/
def condSelCheck : Bool :=
  (List.range 8).all fun j =>
    match selD (16 * j + 16) Sym.init (blkReg (8 + j)) .xmm2 (64 * j) with
    | some σ =>
      ((List.range 16).all fun i =>
        σ.mem 2 (16 * j + i) == .xor (.inp (16 * j + i)) (.reg (xidx (blkReg (8 + j))) i)) &&
      ((List.range (16 * j)).all fun i => σ.mem 2 i == .mem 2 i) &&
      ((List.range 16).all fun i => σ.mem 1 i == .mem 1 i) &&
      (List.range 8).all fun l => (List.range 16).all fun p =>
        σ.reg (xidx (blkReg (8 + l))) p == .reg (xidx (blkReg (8 + l))) p
    | none => false

theorem finishPSelCheck_eq : finishPSelCheck = true := by decide +kernel
theorem condSelCheck_eq : condSelCheck = true := by decide +kernel

/-! ## The output -/

/-- The first eight blocks into the data, from either buffer; the next eight
left in registers. -/
theorem finishPSel_ok {s : State} (hc : Ctx 128 s) (hs : Avx512Tail.SelOk 128 s) (hi : Incs s.mem (s.gpr .r9))
    {vs : Nat → CState} (hz : ZH vs s) :
    WP isa (pieces finishPSel) s fun s' =>
      (∀ k < 512, s'.mem (s.gpr .rsi + BitVec.ofNat 64 k) =
        (if 64 * (k / 64) + 64 ≤ (s.gpr .r10).toNat then s.mem (s.gpr .r8 + BitVec.ofNat 64 k)
          else s.mem (s.gpr .rsi + BitVec.ofNat 64 k)) ^^^
        (serialize (plus vs (S0 s) (k / 64))).getD (k % 64) 0) ∧
      (∀ j < 8, ∀ p (hp : p < 16), zw s' (blkReg (8 + j)) p = (plus vs (S0 s) (8 + j))[p]'hp) ∧
      Frame (wregs 128 s) s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e := finishPSelCheck_eq
  unfold finishPSelCheck at e
  split at e
  · rename_i σ hr
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at e
    refine WP.mono (Avx512Tail.runPieces_ok hc hs _ (SRel.init 128 s) hr) fun s' h => ⟨fun k hk => ?_,
      fun j hj p hp => ?_, h.frame, h.gpr, h.rd, h.wr⟩
    · have d := h.mem 2 (k / 4) (by decide) (by simp only [bsize]; omega_arith)
      rw [e.1 _ (by omega_arith)] at d
      simp only [Avx512Tail.T.eval, regn, baseR] at d
      rw [show k / 4 / 16 = k / 64 by omega_arith, show k / 4 % 16 = k % 64 / 4 by omega_arith,
        outT_eval hz hi (by omega_arith) (by omega_arith)] at d
      rw [byte_dword s'.mem, d, BitVec.extractLsb'_xor, inpW_byte,
        serialize_getD _ (Nat.mod_lt _ (by decide)), show k % 64 % 4 = k % 4 by omega_arith]
    · rw [h.reg _ p hp, e.2 j hj p hp, outT_eval hz hi hp (by omega_arith)]
  · cases e

/-! ## The next eight blocks, as far as they fit -/

theorem condSel_run {j : Nat} (hj : j < 8) : ∃ σ, selD (16 * j + 16) Sym.init (blkReg (8 + j)) .xmm2 (64 * j) = some σ ∧
    (∀ i < 16, σ.mem 2 (16 * j + i) = .xor (.inp (16 * j + i)) (.reg (xidx (blkReg (8 + j))) i)) ∧
    (∀ i < 16 * j, σ.mem 2 i = .mem 2 i) ∧ (∀ i < 16, σ.mem 1 i = .mem 1 i) ∧
    (∀ l < 8, ∀ p < 16, σ.reg (xidx (blkReg (8 + l))) p = .reg (xidx (blkReg (8 + l))) p) := by
  have e := condSelCheck_eq
  simp only [condSelCheck, List.all_eq_true, List.mem_range] at e
  obtain e := e j hj
  split at e
  · rename_i σ hr
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at e
    exact ⟨σ, hr, e.1.1.1, e.1.1.2, e.1.2, e.2⟩
  · cases e

/-- Where `condSel` runs: the data from byte `q` on (fewer than 512 bytes of
it left), `buf` at `r9`, `src` from byte `q` on at `r8`, and `r10` the bytes
of `C` from `q` on. -/
structure AtS (s₀ : State) (C q : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = sst s₀
  r9 : s.gpr .r9 = sbp s₀
  rsi : s.gpr .rsi = sdp s₀ + BitVec.ofNat 64 q
  rdx : s.gpr .rdx = BitVec.ofNat 64 (sL s₀ - q)
  le : q ≤ sL s₀
  small : sL s₀ - q < 512
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  r8 : s.gpr .r8 = ssp s₀ + BitVec.ofNat 64 q
  r10 : s.gpr .r10 = BitVec.ofNat 64 (C - q)
  frame : Frame [stR s₀, sdR s₀, bufR s₀] s₀.mem s.mem

theorem AtS.at_ {s₀ : State} {C q : Nat} {s : State} (h : AtS s₀ C q s) : At (V s₀) q s :=
  ⟨h.rdi, h.r9, h.rsi, h.rdx, h.le, h.small, h.rd, h.wr⟩

theorem AtS.of_gpr {s₀ : State} {C q : Nat} {s s' : State} (h : AtS s₀ C q s) (hg : s'.gpr = s.gpr)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame [stR s₀, sdR s₀, bufR s₀] s₀.mem s'.mem) :
    AtS s₀ C q s' :=
  ⟨by rw [hg]; exact h.rdi, by rw [hg]; exact h.r9, by rw [hg]; exact h.rsi, by rw [hg]; exact h.rdx, h.le,
    h.small, hrd.trans h.rd, hwr.trans h.wr, by rw [hg]; exact h.r8, by rw [hg]; exact h.r10, hf⟩

/-- Where the code around the rounds runs in place (`V s₀`'s destination is
its source), `D` doublewords of data from byte `p`. -/
theorem ctxD_of {s₀ : State} (hp : Avx2.TPre s₀) (he : Avx2.edq s₀ = Avx2.edp s₀) {D p : Nat}
    (hw : p + 4 * D ≤ Avx2.eL s₀) (hD : D ≤ 128) {s : State} (hrdi : s.gpr .rdi = Avx2.est s₀)
    (hr9 : s.gpr .r9 = Avx2.ebp s₀) (hrsi : s.gpr .rsi = Avx2.edp s₀ + BitVec.ofNat 64 p) (hwr : s.wr = s₀.wr) :
    Ctx D s := by
  obtain hL := Avx2.eL_lt s₀
  obtain r0 : regn D s 0 = Avx2.stR (Avx2.est s₀) := by simp only [regn, baseR, bsize, hrdi, Nat.reduceMul]
  obtain r1 : regn D s 1 = Avx2.bufR (Avx2.ebp s₀) := by simp only [regn, baseR, bsize, hr9, Nat.reduceMul]
  obtain r2 : regn D s 2 = winS s₀ p (4 * D) := by simp only [regn, baseR, bsize, hrsi]
  obtain hd : Avx2.edR s₀ ∈ s₀.wr := by
    have := hp.w_q; simp only [Avx2.eqR, he] at this; exact this
  refine ⟨fun b i n hb h _ => ?_, fun b b' hb hb' ne => ?_, hD⟩
  · rw [hwr]
    rcases (by omega_arith : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;> simp only [bsize] at h
    · rw [r0]
      exact ⟨Avx2.stR (Avx2.est s₀), hp.w_st, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    · rw [r1]
      exact ⟨Avx2.bufR (Avx2.ebp s₀), hp.w_b, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    · rw [r2, add_ofNat]
      exact ⟨Avx2.edR s₀, hd, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · have d01 := hp.st_b
    obtain d02 := hp.st_d.sub_right (winS_sub (s₀ := s₀) (p := p) (n := 4 * D) hw)
    obtain d12 := hp.d_b.symm.sub_right (winS_sub (s₀ := s₀) (p := p) (n := 4 * D) hw)
    rcases (by omega_arith : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;>
      rcases (by omega_arith : b' = 0 ∨ b' = 1 ∨ b' = 2) with rfl | rfl | rfl <;>
      simp only [r0, r1, r2] <;>
      first | exact absurd rfl ne | with_reducible assumption | exact d01.symm | exact d02.symm | exact d12.symm

/-- The bytes of `src` a selected load in the last pass may read. -/
theorem selOkD_of {s₀ : State} (hp : APre s₀) {C : Nat} (hC : COk s₀ C) {q D : Nat} (hD : q + 4 * D ≤ sL s₀)
    {s : State} (hr9 : s.gpr .r9 = sbp s₀) (hrsi : s.gpr .rsi = sdp s₀ + BitVec.ofNat 64 q)
    (hr8 : s.gpr .r8 = ssp s₀ + BitVec.ofNat 64 q) (hr10 : s.gpr .r10 = BitVec.ofNat 64 (C - q))
    (hrd : s.rd = s₀.rd) : Avx512Tail.SelOk D s := by
  obtain hS := sS_lt s₀
  obtain hL := sL_lt s₀
  obtain e10 : (s.gpr .r10).toNat = C - q := by
    rw [hr10, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hC.le; omega_using [hS, this])]
  obtain con : ∀ a n, 0 < n → (srcR s).Contains a n → (srR s₀).Contains a n := fun a n hn ha => by
    have hw := hp.wrap_s
    have hc := hC.le
    simp only [srcR, hr8, e10, Region.Contains] at ha ⊢
    obtain e : (a - ssp s₀).toNat = (a - (ssp s₀ + BitVec.ofNat 64 q)).toNat + q := by
      have : q < 2 ^ 64 := by omega_using [hD, hL]
      bv_omega
    omega_using [hn, hc, ha, e]
  obtain sub : Region.Sub (srcR s) (srR s₀) := fun a ha => con a 1 (by decide) ha
  refine ⟨fun a n hn ha => ?_, fun r hr => ?_⟩
  · rw [hrd, hp.rd]
    exact ⟨srR s₀, by simp, con a n hn ha⟩
  · simp only [wregs, hr9, hrsi, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hp.s_b.sub_left sub).sub_right (Region.sub_prefix (by omega_using []))
    · exact (hp.s_d.sub_left sub).sub_right (winQ_sub (s₀ := V s₀) hD)

/-- Block `8 + j` into the data from either buffer, if it fits, or else into
`buf`. -/
theorem condSel_ok {s₀ : State} (hp : APre s₀) {C : Nat} (hC : COk s₀ C) {q j : Nat} (hj : j < 8) {s : State}
    (h : AtS s₀ C q s) {B : CState} (hB : ∀ p (hp : p < 16), zw s (blkReg (8 + j)) p = B[p]'hp) :
    WP isa (condSel j) s fun s' => AtS s₀ C q s' ∧ s'.gpr = s.gpr ∧
      (∀ l < 8, ∀ p < 16, zw s' (blkReg (8 + l)) p = zw s (blkReg (8 + l)) p) ∧
      (∀ k < sL s₀ - q, s'.mem (sdp s₀ + BitVec.ofNat 64 q + BitVec.ofNat 64 k) =
        if 64 * j + 64 ≤ sL s₀ - q ∧ k / 64 = j then
          (if 64 * j + 64 ≤ C - q then s.mem (ssp s₀ + BitVec.ofNat 64 q + BitVec.ofNat 64 k)
            else s.mem (sdp s₀ + BitVec.ofNat 64 q + BitVec.ofNat 64 k)) ^^^ (serialize B).getD (k % 64) 0
        else s.mem (sdp s₀ + BitVec.ofNat 64 q + BitVec.ofNat 64 k)) ∧
      (∀ k < 64, s'.mem (sbp s₀ + BitVec.ofNat 64 k) =
        if 64 * j + 64 ≤ sL s₀ - q then s.mem (sbp s₀ + BitVec.ofNat 64 k) else (serialize B).getD k 0) ∧
      Frame [Avx2.bufR (sbp s₀), winQ (V s₀) q (sL s₀ - q)] s.mem s'.mem := by
  obtain hV := V_TPre hp
  obtain hL := sL_lt s₀
  obtain hS := sS_lt s₀
  have hle := h.le
  have hsm := h.small
  have hCS := hC.le
  have hLV : Avx2.eL (V s₀) = sL s₀ := rfl
  obtain fr : ∀ {m : Mem}, Frame [Avx2.bufR (sbp s₀), winQ (V s₀) q (sL s₀ - q)] s.mem m →
      Frame [stR s₀, sdR s₀, bufR s₀] s₀.mem m := fun hf => h.frame.trans (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨bufR s₀, by simp, fun _ h => h⟩
    · exact ⟨sdR s₀, by simp, winQ_sub (s₀ := V s₀) (by omega_arith)⟩)
  refine WP.seq (WP.mono (cmpJ_ok hj h.at_) fun s₁ ⟨g₁, m₁, rd₁, wr₁, z₁, c₁'⟩ => ?_)
  have c₁ : s₁.cf = some (decide (sL s₀ - q < 64 * j + 64)) := c₁'
  obtain h₁ : AtS s₀ C q s₁ := h.of_gpr g₁ rd₁ wr₁ (by rw [m₁]; exact h.frame)
  obtain nb : ∀ k < sL s₀ - q, ¬ (⟨sbp s₀, 256⟩ : Region).Contains (sdp s₀ + BitVec.ofNat 64 q + BitVec.ofNat 64 k) 1 :=
    fun k hk hc => hp.d_b _ (by rw [add_ofNat]; exact Avx2.in_dR (s₀ := V s₀) (by omega_arith))
      (bufR_sub _ (by omega_arith) _ hc)
  refine WP.ite (decide (sL s₀ - q < 64 * j + 64)) (by simp [eval, c₁]) (fun hs => ?_) (fun hs => ?_)
  · -- The block does not fit: into `buf`.
    simp only [decide_eq_true_eq] at hs
    obtain ⟨σ, hr, hm, hk⟩ := condS_run hj
    obtain hc : Ctx 0 s₁ := ctxD_of hV rfl (D := 0) (p := q) (by omega_arith) (by decide) h₁.rdi
      h₁.r9 h₁.rsi h₁.wr
    refine WP.mono (srun_ok hc _ (SRel.init 0 s₁) hr) fun s₂ e => ?_
    obtain F : Frame [Avx2.bufR (sbp s₀), winQ (V s₀) q (sL s₀ - q)] s.mem s₂.mem := by
      rw [← m₁]
      refine e.frame.sub fun r hr => ?_
      simp only [Avx512Tail.wregsT, wregs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨Avx2.bufR (sbp s₀), by simp, by rw [h₁.r9]; exact bufR_sub _ (by omega_arith)⟩
      · refine ⟨winQ (V s₀) q (sL s₀ - q), by simp, ?_⟩
        intro x hx; simp [Region.Contains] at hx
    refine ⟨h₁.of_gpr e.gpr e.rd e.wr (fr F), e.gpr.trans g₁, fun l hl p hp' => ?_, fun k hk => ?_,
      fun k hk => ?_, F⟩
    · rw [e.reg _ p hp', hk l hl p hp']
      simp only [Avx512Tail.T.eval, Avx512.zreg_xidx, z₁]
    · rw [ite_eq_right (by omega_arith), e.frame _ (by
        intro r hr; simp only [Avx512Tail.wregsT, wregs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.r9]; exact nb k hk
        · simp [Region.Contains]), m₁]
    · rw [ite_eq_right (by omega_arith)]
      obtain d := e.mem 1 (k / 4) (by decide) (by simp only [bsize]; omega_arith)
      rw [hm _ (by omega_arith)] at d
      simp only [Avx512Tail.T.eval, regn, baseR, Avx512.zreg_xidx, h₁.r9, z₁, hB _ (by omega_arith : k / 4 < 16)] at d
      rw [byte_dword s₂.mem, d, serialize_getD _ hk]
  · -- The block fits: into the data.
    simp only [decide_eq_false_iff_not] at hs
    obtain ⟨σ, hr, hx, hlo, hbuf, hk⟩ := condSel_run hj
    obtain hc : Ctx (16 * j + 16) s₁ := ctxD_of hV rfl (p := q) (by omega_arith) (by omega_arith) h₁.rdi
      h₁.r9 h₁.rsi h₁.wr
    obtain hsel : Avx512Tail.SelOk (16 * j + 16) s₁ := selOkD_of hp hC (by omega_arith) h₁.r9 h₁.rsi h₁.r8
      h₁.r10 h₁.rd
    obtain e10 : (s₁.gpr .r10).toNat = C - q := by
      rw [h₁.r10, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    refine WP.mono (Avx512Tail.sel_ok hc hsel (SRel.init _ s₁) hr) fun s₂ e => ?_
    obtain F : Frame [Avx2.bufR (sbp s₀), winQ (V s₀) q (sL s₀ - q)] s.mem s₂.mem := by
      rw [← m₁]
      refine e.frame.sub fun r hr => ?_
      simp only [Avx512Tail.wregsT, wregs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨Avx2.bufR (sbp s₀), by simp, by rw [h₁.r9]; exact bufR_sub _ (by omega_arith)⟩
      · refine ⟨winQ (V s₀) q (sL s₀ - q), by simp, ?_⟩
        rw [h₁.rsi]
        exact Region.sub_prefix (by omega_arith)
    refine ⟨h₁.of_gpr e.gpr e.rd e.wr (fr F), e.gpr.trans g₁, fun l hl p hp' => ?_, fun k hk => ?_,
      fun k hk => ?_, F⟩
    · rw [e.reg _ p hp', hk l hl p hp']
      simp only [Avx512Tail.T.eval, Avx512.zreg_xidx, z₁]
    · rw [byte_dword s₂.mem, ← m₁]
      by_cases hkj : k / 64 = j
      · rw [ite_eq_left ⟨by omega_arith, hkj⟩]
        obtain d := e.mem 2 (k / 4) (by decide) (by simp only [bsize]; omega_arith)
        rw [show k / 4 = 16 * j + k % 64 / 4 by omega_arith, hx _ (by omega_arith)] at d
        simp only [Avx512Tail.T.eval, regn, baseR, Avx512.zreg_xidx, z₁, h₁.rsi,
          hB _ (by omega_arith : k % 64 / 4 < 16)] at d
        rw [show 4 * (16 * j + k % 64 / 4) = 4 * (k / 4) by omega_arith,
          show 16 * j + k % 64 / 4 = k / 4 by omega_arith] at d
        rw [d, BitVec.extractLsb'_xor, inpW_byte, serialize_getD _ (Nat.mod_lt _ (by decide)),
          show k % 64 % 4 = k % 4 by omega_arith, e10, h₁.r8, h₁.rsi, hkj]
      · rw [ite_eq_right (by omega_arith)]
        by_cases hlt : k < 64 * j
        · have d := e.mem 2 (k / 4) (by decide) (by simp only [bsize]; omega_arith)
          rw [hlo _ (by omega_arith)] at d
          simp only [Avx512Tail.T.eval, Avx512Tail.memBase_2, regn, baseR, h₁.rsi] at d
          rw [d, ← byte_dword]
        · rw [← byte_dword s₂.mem]
          refine e.frame _ ?_
          intro r hr; simp only [Avx512Tail.wregsT, wregs, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · rw [h₁.r9]; exact nb k hk
          · rw [h₁.rsi]
            simp only [Region.Contains]
            rw [show sdp s₀ + BitVec.ofNat 64 q + BitVec.ofNat 64 k - (sdp s₀ + BitVec.ofNat 64 q) =
              BitVec.ofNat 64 k by bv_omega, toNat_ofNat_lt (by omega_arith)]
            omega_arith
    · rw [ite_eq_left (by omega_arith), byte_dword s₂.mem, byte_dword s.mem, ← m₁]
      obtain d := e.mem 1 (k / 4) (by decide) (by simp only [bsize]; omega_arith)
      rw [hbuf _ (by omega_arith)] at d
      simp only [Avx512Tail.T.eval, Avx512Tail.memBase_1, regn, baseR, h₁.r9] at d
      rw [d]

/-- Before `condsSel n`, from `sC`: blocks `8 + n` to 15 done (the input
XORed into the data if they fit; the one the data ends in, if any, into
`buf`), blocks `8 + l`, `l < n`, still in their registers. -/
structure CIS (s₀ : State) (C q : Nat) (B : Nat → CState) (sC : State) (n : Nat) (s : State) : Prop where
  at_ : AtS s₀ C q s
  gpr : s.gpr = sC.gpr
  regs : ∀ l < n, ∀ p (hp : p < 16), zw s (blkReg (8 + l)) p = (B l)[p]'hp
  data : ∀ k < sL s₀ - q, s.mem (sdp s₀ + BitVec.ofNat 64 q + BitVec.ofNat 64 k) =
    if n ≤ k / 64 ∧ 64 * (k / 64) + 64 ≤ sL s₀ - q then
      I s₀ (q + k) ^^^ (serialize (B (k / 64))).getD (k % 64) 0
    else sC.mem (sdp s₀ + BitVec.ofNat 64 q + BitVec.ofNat 64 k)
  buf : n ≤ (sL s₀ - q) / 64 → ∀ k < 64,
    s.mem (sbp s₀ + BitVec.ofNat 64 k) = (serialize (B ((sL s₀ - q) / 64))).getD k 0
  frame : Frame [Avx2.bufR (sbp s₀), winQ (V s₀) q (sL s₀ - q)] sC.mem s.mem

theorem condsSel_ok {s₀ : State} (hp : APre s₀) {C : Nat} (hC : COk s₀ C) {q : Nat} (hq : q % 64 = 0)
    {B : Nat → CState} {sC : State}
    (hsC : ∀ k < sL s₀ - q, C ≤ q + k → sC.mem (sdp s₀ + BitVec.ofNat 64 q + BitVec.ofNat 64 k) = I s₀ (q + k)) :
    ∀ n ≤ 8, ∀ {s : State}, CIS s₀ C q B sC n s → WP isa (condsSel n) s (CIS s₀ C q B sC 0)
  | 0, _, _, h => WP.block_nil h
  | n + 1, hn, s, h => by
    obtain hS := sS_lt s₀
    have hCS := hC.le
    have hC64 := hC.dvd
    have hle := h.at_.le
    refine WP.seq (WP.mono (condSel_ok hp hC (j := n) (by omega_arith) h.at_ (h.regs n (by omega_arith)))
      fun s' ⟨a', g', z', d', b', f'⟩ => condsSel_ok hp hC hq hsC n (by omega_arith)
        ⟨a', g'.trans h.gpr, fun l hl p hp' => ?_, fun k hk => ?_, fun hq' k hk => ?_, h.frame.trans f'⟩)
    · rw [z' l (by omega_arith) p hp']; exact h.regs l (by omega_arith) p hp'
    · rw [d' k hk]
      by_cases hkn : k / 64 = n
      · by_cases hf : 64 * n + 64 ≤ sL s₀ - q
        · rw [ite_eq_left ⟨hf, hkn⟩,
            ite_eq_left (c := n ≤ k / 64 ∧ 64 * (k / 64) + 64 ≤ sL s₀ - q) ⟨by omega_arith, by omega_arith⟩, hkn]
          congr 1
          by_cases hsrc : 64 * n + 64 ≤ C - q
          · rw [ite_eq_left hsrc, add_ofNat, src_frame hp h.at_.frame (by omega_arith)]
            simp only [I, show q + k < sS s₀ by omega_arith, ite_true]
          · rw [ite_eq_right hsrc, h.data k hk, ite_eq_right (by omega_arith), hsC k hk (by omega_arith)]
        · rw [ite_eq_right (by omega_arith), ite_eq_right (by omega_arith), h.data k hk,
            ite_eq_right (by omega_arith)]
      · rw [ite_eq_right (by omega_arith : ¬ (64 * n + 64 ≤ sL s₀ - q ∧ k / 64 = n)), h.data k hk]
        by_cases hc : n + 1 ≤ k / 64 ∧ 64 * (k / 64) + 64 ≤ sL s₀ - q
        · rw [ite_eq_left hc, ite_eq_left ⟨by omega_arith, hc.2⟩]
        · rw [ite_eq_right hc, ite_eq_right (by omega_arith)]
    · rw [b' k hk]
      by_cases hf : 64 * n + 64 ≤ sL s₀ - q
      · rw [ite_eq_left hf]; exact h.buf (by omega_arith) k hk
      · rw [ite_eq_right hf, show (sL s₀ - q) / 64 = n by omega_arith]

/-! ## The whole pass -/

theorem last16Sel_eq : last16Sel = .seq (.block (([.mov .r9 (.reg .rcx)] : List Instr) ++ setupB .r9))
    (.seq (rounds 10) (.seq (pieces finishPSel) (.seq (.block (adv512 ++
      (([.alu .add .r8 (.imm (BitVec.ofNat 32 512))] : List Instr) ++ subSat 512)))
    (.seq (condsSel 8) (.seq (.block adv)
      (.seq (Impl.ChaCha20.X86_64.XorBuf.xorBuf .rsi .r9) (.block [.vop .vzeroupper, .mov .rsi (.reg .r9)]))))))) := rfl

theorem V_KS {s₀ : State} (hp : APre s₀) : Avx2.KS (V s₀) = keystream (stateAt s₀.mem (sst s₀)) (sL s₀) := by
  show keystream (Avx2.S0 (V s₀)) (sL s₀) = _
  rw [V_S0 hp]

theorem last16Sel_ok {s₀ : State} (hp : APre s₀) {C : Nat} (hC : COk s₀ C) {t : Nat}
    (hgt : 512 < sL s₀ - 1024 * t) (hlt : sL s₀ - 1024 * t < 1024) {s : State} (h : SInv s₀ C t s) :
    WP isa last16Sel s fun s' =>
      gprPreserved (V s₀) s' ∧ (xorTo 16).post (V s₀) s' := by
  obtain hV := V_TPre hp
  obtain hL := sL_lt s₀
  obtain hS := sS_lt s₀
  have hCS := hC.le
  have hC64 := hC.dvd
  have hLV : Avx2.eL (V s₀) = sL s₀ := rfl
  have hle := h.le
  have hSL := hp.le
  rw [last16Sel_eq]
  -- The sixteen input states.
  refine WP.seq (WP.block_append (WP.mono (mov_ok s) fun s₁ ⟨r9₁, g₁, m₁, rd₁, wr₁, _⟩ => ?_))
  have gk₁ : ∀ r, r ≠ .r9 → s₁.gpr r = s.gpr r := g₁
  obtain r9₁' : s₁.gpr .r9 = sbp s₀ := by rw [r9₁, h.rcx]
  obtain hc₁ : Ctx 0 s₁ := ctxD_of hV rfl (p := 1024 * t) (by omega_arith) (by decide)
    (by rw [gk₁ _ (by decide)]; exact h.rdi) r9₁' (by rw [gk₁ _ (by decide)]; exact h.rsi) (wr₁.trans h.wr)
  obtain hi₁ : Incs s₁.mem (s₁.gpr .r9) := by rw [m₁, r9₁']; exact h.incs
  refine WP.mono (Avx512Last.setup_ok hc₁ hi₁) fun s₂ ⟨hz₂, m₂, g₂, rd₂, wr₂⟩ => ?_
  -- The rounds.
  refine WP.seq (WP.mono (Avx512.rounds_ok hz₂ 10) fun s₃ ⟨hz₃, sm₃⟩ => ?_)
  obtain g₃ : s₃.gpr = s₁.gpr := sm₃.gpr.trans g₂
  obtain m₃ : s₃.mem = s.mem := sm₃.mem.trans (m₂.trans m₁)
  obtain rd₃ : s₃.rd = s₀.rd := sm₃.rd.trans (rd₂.trans (rd₁.trans h.rd))
  obtain wr₃ : s₃.wr = s₀.wr := sm₃.wr.trans (wr₂.trans (wr₁.trans h.wr))
  obtain rdi₃ : s₃.gpr .rdi = sst s₀ := by rw [g₃, gk₁ _ (by decide)]; exact h.rdi
  obtain rsi₃ : s₃.gpr .rsi = sdp s₀ + BitVec.ofNat 64 (1024 * t) := by rw [g₃, gk₁ _ (by decide)]; exact h.rsi
  obtain rdx₃ : s₃.gpr .rdx = BitVec.ofNat 64 (sL s₀ - 1024 * t) := by rw [g₃, gk₁ _ (by decide)]; exact h.rdx
  obtain r8₃ : s₃.gpr .r8 = ssp s₀ + BitVec.ofNat 64 (1024 * t) := by rw [g₃, gk₁ _ (by decide)]; exact h.r8
  obtain r10₃ : s₃.gpr .r10 = BitVec.ofNat 64 (C - 1024 * t) := by rw [g₃, gk₁ _ (by decide)]; exact h.r10
  obtain r9₃ : s₃.gpr .r9 = sbp s₀ := by rw [g₃]; exact r9₁'
  obtain hS₁ : S0 s₁ = ctr (stateAt s₀.mem (sst s₀)) (16 * t) := by
    simp only [S0, m₁, gk₁ _ (by decide : Reg.rdi ≠ .r9), h.rdi]; exact h.cnt
  obtain hS₃ : S0 s₃ = ctr (stateAt s₀.mem (sst s₀)) (16 * t) := by simp only [S0, m₃, rdi₃]; exact h.cnt
  -- The output: eight blocks into the data, eight into registers.
  obtain hc₃ : Ctx 128 s₃ := ctxD_of hV rfl (p := 1024 * t) (by omega_arith) (by decide) rdi₃ r9₃ rsi₃ wr₃
  obtain hs₃ : Avx512Tail.SelOk 128 s₃ := selOkD_of hp hC (q := 1024 * t) (by omega_arith) r9₃ rsi₃ r8₃ r10₃
    (by rw [rd₃])
  obtain hi₃ : Incs s₃.mem (s₃.gpr .r9) := by rw [m₃, r9₃]; exact h.incs
  refine WP.seq (WP.mono (finishPSel_ok hc₃ hs₃ hi₃ hz₃) fun s₄ ⟨d₄, z₄, f₄, g₄, rd₄, wr₄⟩ => ?_)
  refine WP.seq (WP.block_append (WP.mono (adv512_ok (s₀ := V s₀) (p := 1024 * t) (s := s₄) (by omega_arith)
    (by rw [g₄]; exact rsi₃) (by rw [g₄]; exact rdx₃))
    fun s₅' ⟨rsi₅', rdx₅', g₅', z₅', m₅', rd₅', wr₅'⟩ => ?_))
  refine WP.mono (advSel_ok s₅' (n := 512) (c := C - 1024 * t) (by decide) (by omega_arith)
    (by rw [g₅' _ (by decide) (by decide), g₄]; exact r10₃))
    fun s₅ ⟨r8₅, r10₅, g₅, m₅, rd₅, wr₅, z₅⟩ => ?_
  obtain gk₅ : ∀ r, r ≠ .rsi → r ≠ .rdx → r ≠ .rax → r ≠ .r8 → r ≠ .r10 → s₅.gpr r = s₃.gpr r :=
    fun r a b c d e => by rw [g₅ r c d e, g₅' r a b, g₄]
  rw [show wregs 128 s₃ = [⟨sbp s₀, 256⟩, winQ (V s₀) (1024 * t) 512] by
    simp only [wregs, r9₃, rsi₃, winQ, Nat.reduceMul]; rfl] at f₄
  obtain ⟨B, hBd⟩ : ∃ B : Nat → CState,
      B = fun l => plus (fun j => Nat.repeat Spec.ChaCha20.innerBlock 10 (ctr (S0 s₁) j)) (S0 s₃) (8 + l) :=
    ⟨_, rfl⟩
  obtain F₅ : Frame [stR s₀, sdR s₀, bufR s₀] s₀.mem s₅.mem := by
    rw [m₅, m₅']
    refine h.frame.trans ?_
    rw [← m₃]
    refine f₄.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨bufR s₀, by simp, bufR_sub _ (by omega_arith)⟩
    · exact ⟨sdR s₀, by simp, winQ_sub (s₀ := V s₀) (by omega_arith)⟩
  obtain A₅ : AtS s₀ C (1024 * t + 512) s₅ :=
    ⟨by rw [gk₅ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact rdi₃,
      by rw [gk₅ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact r9₃,
      by rw [g₅ _ (by decide) (by decide) (by decide)]; exact rsi₅',
      by rw [g₅ _ (by decide) (by decide) (by decide)]; exact rdx₅', by omega_arith, by omega_arith,
      rd₅.trans (rd₅'.trans (rd₄.trans rd₃)), wr₅.trans (wr₅'.trans (wr₄.trans wr₃)),
      by rw [r8₅, g₅' _ (by decide) (by decide), g₄, r8₃, add_ofNat],
      by rw [r10₅, Nat.sub_sub], F₅⟩
  obtain C₅ : CIS s₀ C (1024 * t + 512) B s₅ 8 s₅ := ⟨A₅, rfl,
    fun l hl q hq => by rw [z₅, z₅', hBd]; exact z₄ l hl q hq,
    fun k hk => by rw [ite_eq_right (by omega_arith)], fun hq => absurd hq (by omega_arith), Frame.refl _ _⟩
  -- The data before this pass's ninth block, as `finishPSel` left it.
  obtain early : ∀ k < 1024 * t + 512, s₅.mem (sdp s₀ + BitVec.ofNat 64 k) =
      I s₀ k ^^^ (keystream (stateAt s₀.mem (sst s₀)) (sL s₀)).getD k 0 := by
    intro k hk
    rw [m₅, m₅']
    by_cases hkp : k < 1024 * t
    · rw [f₄ _ (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact fun hc => hp.d_b _ (Avx2.in_dR (s₀ := V s₀) (by omega_arith)) (bufR_sub _ (by omega_arith) _ hc)
        · exact not_winQ (s₀ := V s₀) (by omega_arith) (by omega_arith) (.inl hkp)), m₃, h.done k hkp]
    · have x := d₄ (k - 1024 * t) (by omega_arith)
      rw [rsi₃, r8₃, r10₃, m₃, sel_byte hp hC h (by omega_arith) (by omega_arith), add_ofNat,
        Nat.add_sub_cancel' (by omega_arith : 1024 * t ≤ k)] at x
      rw [x, hS₃, hS₁, ← V_KS hp, Avx512Tail.ks_at (s₀ := V s₀) (p := 1024 * t) (k := k) ⟨16 * t, by omega_arith⟩
        (by omega_arith) (by omega_arith), show 1024 * t / 64 = 16 * t by omega_arith, V_S0 hp]
  -- The next eight blocks, as far as they fit.
  obtain hsC : ∀ k < sL s₀ - (1024 * t + 512), C ≤ 1024 * t + 512 + k →
      s₅.mem (sdp s₀ + BitVec.ofNat 64 (1024 * t + 512) + BitVec.ofNat 64 k) = I s₀ (1024 * t + 512 + k) := by
    intro k hk hck
    obtain hk' : 1024 * t + 512 + k < sL s₀ := by omega_arith
    rw [add_ofNat, m₅, m₅', f₄ (sdp s₀ + BitVec.ofNat 64 (1024 * t + 512 + k)) (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact fun hc => hp.d_b _ (Avx2.in_dR (s₀ := V s₀) hk') (bufR_sub _ (by omega_arith) _ hc)
        · exact not_winQ (s₀ := V s₀) (by omega_arith) hk' (.inr (by omega_arith))), m₃]
    exact h.todo _ hk' (by omega_arith) hck
  refine WP.seq (WP.mono (condsSel_ok hp hC (by omega_arith) hsC 8 (by decide) C₅) fun s₆ C₆ => ?_)
  refine WP.seq (WP.mono (adv_ok C₆.at_.at_) fun s₇ ⟨rsi₇, rdx₇, g₇, m₇, rd₇, wr₇⟩ => ?_)
  -- The rest, from `buf`.
  obtain r9₇ : s₇.gpr .r9 = sbp s₀ := by rw [g₇ _ (by decide) (by decide) (by decide)]; exact C₆.at_.r9
  obtain keep₇ : ∀ r ∈ calleeSaved, s₇.gpr r = (V s₀).gpr r := fun r hr => by
    obtain ⟨_, a, b, c⟩ := Avx2Tail.r9_not_calleeSaved hr
    obtain ⟨a', b', c', d', e'⟩ := calleeSaved_ne hr
    rw [g₇ r a' b' c', C₆.gpr, gk₅ r b' c' a' d' e', g₃, gk₁ r (Avx512Last.r9_ne hr), V_keep s₀ hr]
    exact h.keep r hr
  obtain hB : ∀ k, 1024 * t + 512 ≤ k → k < sL s₀ →
      (serialize (B ((k - (1024 * t + 512)) / 64))).getD ((k - (1024 * t + 512)) % 64) 0 =
        (keystream (stateAt s₀.mem (sst s₀)) (sL s₀)).getD k 0 := by
    intro k hk₁ hk₂
    rw [← V_KS hp, Avx512Tail.ks_at (s₀ := V s₀) (p := 1024 * t) (k := k) ⟨16 * t, by omega_arith⟩ (by omega_arith) hk₂,
      hBd]
    simp only [hS₃, hS₁]
    rw [V_S0 hp, show 8 + (k - (1024 * t + 512)) / 64 = (k - 1024 * t) / 64 by omega_arith,
      show (k - (1024 * t + 512)) % 64 = (k - 1024 * t) % 64 by omega_arith,
      show 1024 * t / 64 = 16 * t by omega_arith]
  have hmb := C₆.buf
  replace rsi₇ : s₇.gpr .rsi = sdp s₀ + BitVec.ofNat 64 (1024 * t + 512 + 64 * ((sL s₀ - (1024 * t + 512)) / 64)) :=
    rsi₇
  replace rdx₇ : s₇.gpr .rdx =
      BitVec.ofNat 64 (sL s₀ - (1024 * t + 512 + 64 * ((sL s₀ - (1024 * t + 512)) / 64))) := rdx₇
  generalize hm : (sL s₀ - (1024 * t + 512)) / 64 = m at rsi₇ rdx₇ hmb
  refine WP.seq (WP.mono (Avx2Tail.xorBufTo_done (d := .rsi) (by decide) hV (p := 1024 * t + 512 + 64 * m)
    (n := sL s₀ - (1024 * t + 512 + 64 * m))
    (by omega_arith) (by omega_arith) rsi₇ rsi₇ r9₇ rdx₇ (rd₇.trans C₆.at_.rd) (wr₇.trans C₆.at_.wr) keep₇
    (fun k hk => ?_) (fun k hk => ?_) (fun k hk => ?_) ?_) fun s₈ d₈ => Avx2Tail.fin_ok (d₈.fin hV))
  · show s₇.mem (sdp s₀ + BitVec.ofNat 64 k) = Avx2.D0 (V s₀) k ^^^ (Avx2.KS (V s₀)).getD k 0
    rw [m₇, V_D0 s₀ (k := k) (by omega_arith), V_KS hp]
    by_cases hk5 : k < 1024 * t + 512
    · rw [C₆.frame (sdp s₀ + BitVec.ofNat 64 k) (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact fun hc => hp.d_b _ (Avx2.in_dR (s₀ := V s₀) (by omega_arith)) hc
        · exact not_winQ (s₀ := V s₀) (by omega_arith) (by omega_arith) (.inl hk5))]
      exact early k hk5
    · have x := C₆.data (k - (1024 * t + 512)) (by omega_arith)
      rw [add_ofNat, Nat.add_sub_cancel' (by omega_arith : 1024 * t + 512 ≤ k),
        ite_eq_left ⟨Nat.zero_le _, by omega_arith⟩] at x
      rw [x, hB k (by omega_arith) (by omega_arith)]
  · show s₇.mem (sdp s₀ + BitVec.ofNat 64 (1024 * t + 512 + 64 * m) + BitVec.ofNat 64 k) =
      Avx2.D0 (V s₀) (1024 * t + 512 + 64 * m + k)
    obtain ea : sdp s₀ + BitVec.ofNat 64 (1024 * t + 512 + 64 * m) + BitVec.ofNat 64 k =
        sdp s₀ + BitVec.ofNat 64 (1024 * t + 512) + BitVec.ofNat 64 (64 * m + k) := by
      rw [add_ofNat, add_ofNat, Nat.add_assoc]
    obtain x := C₆.data (64 * m + k) (by omega_arith)
    rw [m₇, ea, x, ite_eq_right (by omega_arith), hsC _ (by omega_arith) (by omega_arith),
      V_D0 s₀ (by omega_arith), show 1024 * t + 512 + (64 * m + k) = 1024 * t + 512 + 64 * m + k by omega_arith]
  · show s₇.mem (sbp s₀ + BitVec.ofNat 64 k) = (Avx2.KS (V s₀)).getD (1024 * t + 512 + 64 * m + k) 0
    obtain y := hB (1024 * t + 512 + 64 * m + k) (by omega_arith) (by omega_arith)
    rw [show (1024 * t + 512 + 64 * m + k - (1024 * t + 512)) / 64 = m by omega_arith,
      show (1024 * t + 512 + 64 * m + k - (1024 * t + 512)) % 64 = k by omega_arith] at y
    rw [m₇, V_KS hp, hmb (Nat.zero_le _) k (by omega_arith), y]
  · rw [m₇]
    exact V_frame C₆.at_.frame

end VG.Proof.ChaCha20.X86_64.Avx512Split

end

end


/-!
# ChaCha20 keystream XOR with the data's first bytes from another buffer on x86-64 with AVX-512: the function

The entry (`C`, the copy of the bytes of `src` from `C` on to `dst`, and the
loop's registers), the last bytes after the loop (by a call of
`vg_chacha20_xor_avx512` in place when fewer than 513 are left, as `C` is
then at most where they start, `tailCall_ok`; else by `last16Sel_ok`), and
the postcondition.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Avx512Split

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx512
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.ChaCha20 (Word stateAt keystream serialize bytesAt)
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86_64.Avx2 (add_ofNat)
open VG.WriteBytes (writeBytes writeBytes_frame)
open VG.Proof.AesGcm.X86_64.Short (CopyPre)

/-! ## `C` -/

/-- `C`: `src_len` rounded down to a multiple of 64, and, if fewer than 513
bytes follow the whole 1024-byte passes, at most `len` rounded down to a
multiple of 1024. -/
def Cof (s₀ : State) : Nat :=
  if sL s₀ - 1024 * (sL s₀ / 1024) < 513 then min (64 * (sS s₀ / 64)) (1024 * (sL s₀ / 1024))
  else 64 * (sS s₀ / 64)

theorem Cof_ok {s₀ : State} (hp : APre s₀) : COk s₀ (Cof s₀) := by
  have := hp.le
  unfold Cof; constructor <;> split <;> omega_arith

theorem shr_shl10 (r : Nat) (hr : r < 2 ^ 64) :
    BitVec.ofNat 64 r >>> 10 <<< 10 = BitVec.ofNat 64 (1024 * (r / 1024)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt hr]
  omega_arith

theorem entryA_ok (s₀ : State) :
    WP isa (.block [.mov .rax (.reg .r8), .shift .shr .rax 10, .shift .shl .rax 10,
      .mov .r10 (.reg .rdx), .shift .shr .r10 6, .shift .shl .r10 6,
      .mov .r11 (.reg .r8), .alu .sub .r11 (.reg .rax), .alu .cmp .r11 (.imm 513)]) s₀ fun s =>
      s.gpr .rax = BitVec.ofNat 64 (1024 * (sL s₀ / 1024)) ∧
      s.gpr .r10 = BitVec.ofNat 64 (64 * (sS s₀ / 64)) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → s.gpr r = s₀.gpr r) ∧
      s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
      s.cf = some (decide (sL s₀ - 1024 * (sL s₀ / 1024) < 513)) := by
  obtain hL := sL_lt s₀
  obtain hS := sS_lt s₀
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, execShift, arithFlags,
    State.setReg, State.setFlags, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left',
    reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, and_self]
  obtain e8 : s₀.gpr .r8 = BitVec.ofNat 64 (sL s₀) := by simp [sL]
  obtain e2 : s₀.gpr .rdx = BitVec.ofNat 64 (sS s₀) := by simp [sS]
  obtain se : BitVec.signExtend 64 (513 : BitVec 32) = 513 := by decide
  rw [e8, e2, shr_shl10 _ hL, Avx512Last.shr_shl _ hS, se]
  refine ⟨rfl, rfl, fun r h1 h2 h3 => by simp [h1, h2, h3], trivial, trivial, trivial, ?_⟩
  obtain e : (BitVec.ofNat 64 (sL s₀) - BitVec.ofNat 64 (1024 * (sL s₀ / 1024))).toNat =
      sL s₀ - 1024 * (sL s₀ / 1024) := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt hL,
      Nat.mod_eq_of_lt (by omega_arith)]; omega_arith), BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hL,
      Nat.mod_eq_of_lt (by omega_arith)]
  rw [e]; rfl

theorem entryC_ok (s₀ : State) :
    WP isa entryC s₀ fun s => s.gpr .r10 = BitVec.ofNat 64 (Cof s₀) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → s.gpr r = s₀.gpr r) ∧
      s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  obtain hL := sL_lt s₀
  obtain hS := sS_lt s₀
  refine WP.seq (WP.mono (entryA_ok s₀) fun s₁ ⟨rax₁, r10₁, g₁, m₁, rd₁, wr₁, c₁⟩ => ?_)
  refine WP.ite (decide (sL s₀ - 1024 * (sL s₀ / 1024) < 513)) (by simp [eval, c₁]) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, execCmov, eval, arithFlags,
      State.setReg, State.setFlags, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left',
      rax₁, r10₁]
    obtain ea : (BitVec.ofNat 64 (64 * (sS s₀ / 64))).toNat = 64 * (sS s₀ / 64) := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    obtain eb : (BitVec.ofNat 64 (1024 * (sL s₀ / 1024))).toNat = 1024 * (sL s₀ / 1024) := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    simp only [ea, eb]
    by_cases hab : 64 * (sS s₀ / 64) < 1024 * (sL s₀ / 1024)
    · simp only [hab, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      refine ⟨?_, fun r h1 h2 h3 => g₁ r h1 h2 h3, m₁, rd₁, wr₁⟩
      rw [r10₁]; simp only [Cof, hb, ↓reduceIte, Nat.min_eq_left (Nat.le_of_lt hab)]
    · simp only [hab, decide_false, Bool.not_false, ↓reduceIte]
      refine ⟨?_, fun r h1 h2 h3 => by simp only [h2, ↓reduceIte]; exact g₁ r h1 h2 h3, m₁, rd₁, wr₁⟩
      simp only [Cof, hb, ↓reduceIte, Nat.min_eq_right (by omega_arith : 1024 * (sL s₀ / 1024) ≤ 64 * (sS s₀ / 64))]
  · simp only [decide_eq_false_iff_not] at hb
    exact WP.block_nil (M := isa) ⟨by rw [r10₁]; simp only [Cof, hb, ↓reduceIte], g₁, m₁, rd₁, wr₁⟩

theorem Cof_gap {s₀ : State} (hp : APre s₀) : sS s₀ - Cof s₀ < 1024 := by
  have := hp.le
  unfold Cof; split <;> omega_arith

theorem Cof_le {s₀ : State} (h : sL s₀ - 1024 * (sL s₀ / 1024) < 513) :
    Cof s₀ ≤ 1024 * (sL s₀ / 1024) := by
  unfold Cof; rw [ite_eq_left h]; omega_arith

/-! ## The copy -/

theorem bytesAt_getD' (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hi]

theorem copyArgs_ok {s₀ : State} (hp : APre s₀) {C : Nat} (hC : C ≤ sS s₀) {s : State}
    (hg : ∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → s.gpr r = s₀.gpr r) (hr10 : s.gpr .r10 = BitVec.ofNat 64 C)
    (hwr : s.wr = s₀.wr) :
    WP isa (.block copyArgs) s fun s' =>
      s'.gpr .r11 = sst s₀ ∧ s'.gpr .rdi = sdp s₀ + BitVec.ofNat 64 C ∧
      s'.gpr .rsi = ssp s₀ + BitVec.ofNat 64 C ∧ s'.gpr .rcx = BitVec.ofNat 64 (sS s₀ - C) ∧
      s'.gpr .rdx = BitVec.ofNat 64 C ∧ s'.gpr .r9 = sbp s₀ ∧ s'.gpr .rbx = s₀.gpr .r8 ∧
      (∀ r ∈ calleeSaved, r ≠ .rbx → s'.gpr r = s₀.gpr r) ∧
      s'.mem = s.mem.writeW (sbp s₀) (s₀.gpr .rbx) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain hS := sS_lt s₀
  obtain hea : s.ea (at_ .r9 0) = sbp s₀ := by
    simp only [State.ea, at_, hg .r9 (by decide) (by decide) (by decide)]
    rw [show BitVec.ofInt 64 ((0 : Nat) : Int) = 0#64 by decide, BitVec.add_zero]
  obtain hin : InRegions s.wr (s.ea (at_ .r9 0)) 8 := by
    rw [hea, hwr, hp.wr]; exact ⟨bufR s₀, by simp, by simp [Region.Contains]⟩
  apply WP.of_runBlock
  simp only [copyArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    State.store64, hin, ite_true, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left',
    State.setReg, State.setFlags]
  simp only [reduceCtorEq, ↓reduceIte, hea]
  have g : ∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → s.gpr r = s₀.gpr r := hg
  rw [g .rdi (by decide) (by decide) (by decide), g .rcx (by decide) (by decide) (by decide),
    g .rsi (by decide) (by decide) (by decide), g .rdx (by decide) (by decide) (by decide),
    g .r9 (by decide) (by decide) (by decide), g .r8 (by decide) (by decide) (by decide),
    g .rbx (by decide) (by decide) (by decide), hr10]
  obtain e2 : s₀.gpr .rdx = BitVec.ofNat 64 (sS s₀) := by simp [sS]
  refine ⟨rfl, rfl, rfl, by rw [e2]; bv_omega, rfl, rfl, rfl, fun r hr hb => ?_, rfl, trivial, trivial⟩
  obtain ⟨a, b, c, d, e⟩ := calleeSaved_ne hr
  obtain f : r ≠ .rcx ∧ r ≠ .rdi ∧ r ≠ .r11 := by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  simp only [b, c, f.1, f.2.1, f.2.2, hb]
  exact g r a e f.2.2

theorem loopArgs_ok {s₀ : State} (hp : APre s₀) {C : Nat} {s : State}
    (hr11 : s.gpr .r11 = sst s₀) (hrdi : s.gpr .rdi = sdp s₀ + BitVec.ofNat 64 C)
    (hrsi : s.gpr .rsi = ssp s₀ + BitVec.ofNat 64 C) (hrdx : s.gpr .rdx = BitVec.ofNat 64 C)
    (hr9 : s.gpr .r9 = sbp s₀) (hrbx : s.gpr .rbx = s₀.gpr .r8)
    (hsave : s.mem.readW (sbp s₀) 64 = s₀.gpr .rbx) (hwr : s.wr = s₀.wr) :
    WP isa (.block loopArgs) s fun s' =>
      s'.gpr .rdi = sst s₀ ∧ s'.gpr .rsi = sdp s₀ ∧ s'.gpr .rdx = s₀.gpr .r8 ∧ s'.gpr .rcx = sbp s₀ ∧
      s'.gpr .r8 = ssp s₀ ∧ s'.gpr .r10 = BitVec.ofNat 64 C ∧ s'.gpr .r9 = sbp s₀ ∧
      s'.gpr .rbx = s₀.gpr .rbx ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r10 → r ≠ .rbx →
        s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain hea : s.ea (at_ .r9 0) = sbp s₀ := by
    simp only [State.ea, at_, hr9]
    rw [show BitVec.ofInt 64 ((0 : Nat) : Int) = 0#64 by decide, BitVec.add_zero]
  obtain hin : InRegions (s.rd ++ s.wr) (s.ea (at_ .r9 0)) 8 := by
    rw [hea, hwr, hp.wr]; exact ⟨bufR s₀, by simp, by simp [Region.Contains]⟩
  apply WP.of_runBlock
  simp only [loopArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    State.load64, hin, ite_true, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left',
    State.setReg, State.setFlags]
  simp only [reduceCtorEq, ↓reduceIte, hea, hsave]
  rw [hr11, hrdi, hrsi, hrdx, hr9, hrbx]
  and_intros
  all_goals first
    | trivial | rfl | exact BitVec.add_sub_cancel _ _
    | (intro r h1 h2 h3 h4 h5 h6 h7 h8; simp only [h1, h2, h3, h4, h5, h6, h7, h8, ite_false])

/-! ## The postcondition -/

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by simp [bytesAt]

theorem bytesAt_getElem (m : Mem) (p : Addr) (n i : Nat) (h : i < (bytesAt m p n).length) :
    (bytesAt m p n)[i] = m (p + BitVec.ofNat 64 i) := by simp [bytesAt]

theorem bytes_vmem {s₀ : State} (hp : APre s₀) :
    bytesAt (vmem s₀) (sdp s₀) (sL s₀) =
      bytesAt s₀.mem (ssp s₀) (sS s₀) ++ (bytesAt s₀.mem (sdp s₀) (sL s₀)).drop (sS s₀) := by
  have hSL := hp.le
  apply List.ext_getElem
  · simp only [bytesAt_length, List.length_append, List.length_drop]; omega_arith
  · intro i h₁ h₂
    obtain hi : i < sL s₀ := by rwa [bytesAt_length] at h₁
    rw [bytesAt_getElem, vmem_dst s₀ hi, List.getElem_append]
    unfold I
    by_cases hs : i < sS s₀
    · rw [ite_eq_left hs, dite_eq_left (by rw [bytesAt_length]; exact hs), bytesAt_getElem]
    · rw [ite_eq_right hs, dite_eq_right (by rw [bytesAt_length]; exact hs), List.getElem_drop, bytesAt_getElem,
        bytesAt_length, Nat.add_sub_cancel' (by omega_arith)]

theorem post_of_V {s₀ : State} (hp : APre s₀) {s' : State}
    (h : gprPreserved (V s₀) s' ∧ xorX86_64.post (V s₀) s') :
    gprPreserved s₀ s' ∧ xorSplitX86_64.post s₀ s' := by
  obtain ⟨⟨hk, hr⟩, hpost⟩ := h
  refine ⟨⟨fun r hr' => (hk r hr').trans (V_keep s₀ hr'), ?_⟩, ?_⟩
  · rw [V_rsp, V_mem] at hr
    rw [hr]
    exact ((vmem_frame s₀).readW (r := sret s₀) (a := s₀.gpr .rsp) (w := 64) (Region.contains_self _ _)
      (by intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hp.ret_d) (by decide)).symm
  · simp only [xorX86_64, V_rsi, V_rdx, V_rdi, V_mem] at hpost
    simp only [xorSplitX86_64]
    obtain e : stateAt (vmem s₀) (sst s₀) = stateAt s₀.mem (sst s₀) := V_S0 hp
    rw [hpost, bytes_vmem hp, e]

/-! ## The prologue -/

/-- The bytes of `dst` from `C` on after the copy: the input's. -/
theorem copied_byte {s₀ : State} (hp : APre s₀) {C : Nat} (hC : C ≤ sS s₀) {m : Mem}
    (hm : ∀ k < sS s₀, m (ssp s₀ + BitVec.ofNat 64 k) = s₀.mem (ssp s₀ + BitVec.ofNat 64 k))
    (hd : ∀ k < sL s₀, sS s₀ ≤ k → m (sdp s₀ + BitVec.ofNat 64 k) = s₀.mem (sdp s₀ + BitVec.ofNat 64 k))
    {k : Nat} (hk : k < sL s₀) (hck : C ≤ k) :
    writeBytes m (sdp s₀ + BitVec.ofNat 64 C) (bytesAt m (ssp s₀ + BitVec.ofNat 64 C) (sS s₀ - C))
      (sdp s₀ + BitVec.ofNat 64 k) = I s₀ k := by
  obtain hL := sL_lt s₀
  have hw := hp.wrap_d
  obtain e : (sdp s₀ + BitVec.ofNat 64 k - (sdp s₀ + BitVec.ofNat 64 C)).toNat = k - C := by
    rw [show sdp s₀ + BitVec.ofNat 64 k - (sdp s₀ + BitVec.ofNat 64 C) = BitVec.ofNat 64 (k - C) by
      bv_omega, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  simp only [writeBytes, e, bytesAt_length]
  unfold I
  by_cases hs : k < sS s₀
  · rw [ite_eq_left (by omega_arith), ite_eq_left hs, bytesAt_getD' _ _ (by omega_arith), add_ofNat,
      Nat.add_sub_cancel' hck, hm k hs]
  · rw [ite_eq_right (by omega_arith), ite_eq_right hs, hd k hk (by omega_arith)]

theorem prologue_ok {s₀ : State} (hp : APre s₀) {Q : State → Prop} {rest : Prog isa}
    (hk : ∀ s, SInv s₀ (Cof s₀) 0 s → s.cf = some (decide (sL s₀ < 1024)) → WP isa rest s Q) :
    WP isa (.seq entryC (.seq (.block copyArgs) (.seq (Impl.ChaCha20Poly1305.X86_64.SealGather.copyBytes .z64)
      (.seq (.block (loopArgs ++ Impl.ChaCha20.X86_64.Avx512Tail.consts ++ consts ++
        ([.alu .cmp .rdx (.imm 1024)] : List Instr))) rest)))) s₀ Q := by
  obtain hL := sL_lt s₀
  obtain hS := sS_lt s₀
  have hSL := hp.le
  obtain hCo := Cof_ok hp
  obtain hgap := Cof_gap hp
  have hws := hp.wrap_s
  have hwd := hp.wrap_d
  generalize hCd : Cof s₀ = C at hCo hgap hk
  have hCS := hCo.le
  refine WP.seq (WP.mono (entryC_ok s₀) fun s₁ ⟨r10₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  rw [hCd] at r10₁
  refine WP.seq (WP.mono (copyArgs_ok hp hCS g₁ r10₁ wr₁)
    fun s₂ ⟨r11₂, rdi₂, rsi₂, rcx₂, rdx₂, r9₂, rbx₂, keep₂, m₂, rd₂, wr₂⟩ => ?_)
  obtain cp : CopyPre s₂ (ssp s₀ + BitVec.ofNat 64 C) (sdp s₀ + BitVec.ofNat 64 C) (sS s₀ - C) :=
    ⟨rsi₂, rdi₂, rcx₂, by omega_arith,
      by rw [rd₂, rd₁, hp.rd]
         exact Covers.left (Covers.of_sub fun r hr => by
           simp only [List.mem_singleton] at hr; subst hr
           exact ⟨srR s₀, by simp, C, rfl, by simp only; omega_arith⟩),
      by rw [wr₂, wr₁, hp.wr]
         exact Covers.of_sub fun r hr => by
           simp only [List.mem_singleton] at hr; subst hr
           exact ⟨sdR s₀, by simp, C, rfl, by simp only; omega_arith⟩,
      (hp.s_d.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith))⟩
  refine WP.seq (WP.mono (VG.Proof.ChaCha20Poly1305.X86_64.Gather.copyBytes_ok cp .z64) fun s₃ ⟨m₃, g₃, rd₃, wr₃⟩ => ?_)
  replace m₃ : s₃.mem = writeBytes s₂.mem (sdp s₀ + BitVec.ofNat 64 C)
      (bytesAt s₂.mem (ssp s₀ + BitVec.ofNat 64 C) (sS s₀ - C)) := m₃
  have gk₃ : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → s₃.gpr r = s₂.gpr r := g₃
  -- The memory so far.
  obtain FW : Frame [⟨sdp s₀ + BitVec.ofNat 64 C, sS s₀ - C⟩] s₂.mem s₃.mem := by
    rw [m₃]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  obtain FB : Frame [bufR s₀] s₀.mem s₂.mem := by
    rw [m₂, m₁]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by simp [Region.Contains])
  obtain dsub : Region.Sub ⟨sdp s₀ + BitVec.ofNat 64 C, sS s₀ - C⟩ (sdR s₀) := Offset.sub_base _ (by omega_arith)
  obtain F₃ : Frame [stR s₀, sdR s₀, bufR s₀] s₀.mem s₃.mem :=
    (FB.mono (by simp)).trans (FW.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨sdR s₀, by simp, dsub⟩)
  obtain hlen : s₃.mem.readW (sbp s₀) 64 = s₀.gpr .rbx := by
    rw [FW.readW (r := ⟨sbp s₀, 8⟩) (Region.contains_self _ _) (by
        intro r hr; simp only [List.mem_singleton] at hr; subst hr
        exact (hp.d_b.symm.sub_left (Region.sub_prefix (by omega_arith))).sub_right dsub) (by decide), m₂,
      Mem.readW_writeW_self64]
  rw [Avx512.tconsts_eq, Avx512.consts_eq]
  refine WP.seq (WP.block_append (WP.block_append (WP.block_append (WP.mono (loopArgs_ok hp (C := C)
    (by rw [gk₃ _ (by decide) (by decide) (by decide)]; exact r11₂)
    (by rw [gk₃ _ (by decide) (by decide) (by decide)]; exact rdi₂)
    (by rw [gk₃ _ (by decide) (by decide) (by decide)]; exact rsi₂)
    (by rw [gk₃ _ (by decide) (by decide) (by decide)]; exact rdx₂)
    (by rw [gk₃ _ (by decide) (by decide) (by decide)]; exact r9₂)
    (by rw [gk₃ _ (by decide) (by decide) (by decide)]; exact rbx₂) hlen (wr₃.trans (wr₂.trans wr₁)))
    fun s₄ ⟨rdi₄, rsi₄, rdx₄, rcx₄, r8₄, r10₄, r9₄, rbx₄, g₄, m₄, rd₄, wr₄⟩ =>
      WP.mono (Avx2.pairs_ok Avx512.tPairs Avx512.tPairs_le (buf := sbp s₀) (s := s₄) rcx₄
        (by rw [wr₄, wr₃, wr₂, wr₁, hp.wr]; simp))
      fun s₅ ⟨m₅, g₅, rd₅, wr₅⟩ =>
        WP.mono (Avx2.pairs_ok Avx512.incPairs Avx512.incPairs_le (buf := sbp s₀) (s := s₅)
          (by rw [g₅ _ (by decide)]; exact rcx₄) (by rw [wr₅, wr₄, wr₃, wr₂, wr₁, hp.wr]; simp))
        fun s₆ ⟨m₆, g₆, rd₆, wr₆⟩ => WP.mono (Avx512.cmp_ok s₆) fun s₇ ⟨g₇, m₇, rd₇, wr₇, cf₇⟩ => ?_))))
  obtain gp : ∀ r, r ≠ .rax → s₇.gpr r = s₄.gpr r := fun r h => by rw [g₇, g₆ r h, g₅ r h]
  obtain mm : s₇.mem = Avx2.storeAll (sbp s₀) Avx512.incPairs (Avx2.storeAll (sbp s₀) Avx512.tPairs s₃.mem) := by
    rw [m₇, m₆, m₅, m₄]
  obtain FS : Frame [bufR s₀] s₃.mem s₇.mem := by
    rw [mm]
    exact (Avx2.storeAll_frame (List.mem_singleton_self _) _ Avx512.tPairs_le _).trans
      (Avx2.storeAll_frame (List.mem_singleton_self _) _ Avx512.incPairs_le _)
  obtain Fx : Frame [sdR s₀, bufR s₀] s₀.mem s₇.mem :=
    ((FB.mono (by simp)).trans (FW.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨sdR s₀, by simp, dsub⟩)).trans (FS.mono (by simp))
  obtain nb : ∀ k < sL s₀, ¬ (bufR s₀).Contains (sdp s₀ + BitVec.ofNat 64 k) 1 := fun k hk hc =>
    hp.d_b _ (Avx2.in_dR (s₀ := V s₀) hk) hc
  obtain e0 : ∀ a : Addr, a + BitVec.ofNat 64 (1024 * 0) = a := fun a => by
    rw [Nat.mul_zero, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
  refine hk s₇ ⟨by rw [gp _ (by decide)]; exact rdi₄, by rw [gp _ (by decide)]; exact rcx₄,
    by rw [gp _ (by decide), rsi₄, e0], by rw [gp _ (by decide), rdx₄, Nat.mul_zero, Nat.sub_zero]; simp [sL],
    by rw [gp _ (by decide), r8₄, e0], by rw [gp _ (by decide), r10₄, Nat.mul_zero, Nat.sub_zero], by omega_arith,
    fun r hr => ?_, by rw [rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁], by rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁], ?_,
    fun k hk => absurd hk (by omega_arith), fun k hk _ hck => ?_, by rw [mm]; exact Avx512.incs_mem _ _,
    by rw [mm]; exact Avx512.tincs_mem _ _, (Fx.mono (by simp))⟩ ?_
  · by_cases hb : r = .rbx
    · subst hb; rw [gp _ (by decide)]; exact rbx₄
    obtain ⟨a, b, c, d, e⟩ := calleeSaved_ne hr
    obtain f : r ≠ .rcx ∧ r ≠ .rdi := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [gp r a, g₄ r a f.2 b c f.1 d e hb, gk₃ r a d e]
    exact keep₂ r hr hb
  · rw [Nat.mul_zero, ctr_zero]
    exact Xor.stateAt_frame Fx (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.st_d
      · exact hp.st_b)
  · rw [FS _ (by intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact nb k hk), m₃]
    exact copied_byte hp hCS (fun k hk => by
        rw [m₂, m₁]
        exact (Frame.refl [bufR s₀] _).writeW (List.mem_singleton_self _) _ (by simp [Region.Contains]) _
          (by intro r hr; simp only [List.mem_singleton] at hr; subst hr
              exact fun hc => hp.s_b _ (Offset.contains_base _ (by omega_arith) (by omega_arith)) hc))
      (fun k hk _ => by
        rw [m₂, m₁]
        exact (Frame.refl [bufR s₀] _).writeW (List.mem_singleton_self _) _ (by simp [Region.Contains]) _
          (by intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact nb k hk))
      hk hck
  · rw [cf₇, g₆ .rdx (by decide), g₅ .rdx (by decide), rdx₄]

/-! ## The last bytes -/

theorem SInv.of_eq {s₀ : State} {C t : Nat} {s s' : State} (h : SInv s₀ C t s) (hg : s'.gpr = s.gpr)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : SInv s₀ C t s' :=
  ⟨by rw [hg]; exact h.rdi, by rw [hg]; exact h.rcx, by rw [hg]; exact h.rsi, by rw [hg]; exact h.rdx,
    by rw [hg]; exact h.r8, by rw [hg]; exact h.r10, h.le, fun r hr => by rw [hg]; exact h.keep r hr,
    hrd.trans h.rd, hwr.trans h.wr, by rw [hm]; exact h.cnt, fun k hk => by rw [hm]; exact h.done k hk,
    fun k hk h₁ h₂ => by rw [hm]; exact h.todo k hk h₁ h₂, by rw [hm]; exact h.incs, by rw [hm]; exact h.tincs,
    by rw [hm]; exact h.frame⟩

/-! ## Fewer than 513 bytes left: the call -/

/-- The return address a call stores. -/
theorem callEntry_frame (s : State) : Frame [below (s.gpr .rsp) 8] s.mem s.callEntry.mem := by
  rw [State.callEntry_mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by lit_omega) (by lit_omega))

theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-- A call of the implementation `v` of `vg_chacha20_xor`, with 24 bytes of stack below `rsp`:
8 for its return address, 16 for its calls. -/
theorem xor_call (v : XorImpl) {s : State} {S D B : Addr} {n : Nat}
    (hrdi : s.gpr .rdi = S) (hrsi : s.gpr .rsi = D)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 n) (hrcx : s.gpr .rcx = B) (hn : n < 2 ^ 64)
    (hSD : (⟨S, 64⟩ : Region).Disjoint ⟨D, n⟩) (hSB : (⟨S, 64⟩ : Region).Disjoint ⟨B, 320⟩)
    (hDB : (⟨D, n⟩ : Region).Disjoint ⟨B, 320⟩) (hwrap : D.toNat + n ≤ 2 ^ 64)
    (hsS : (below (s.gpr .rsp) 24).Disjoint ⟨S, 64⟩) (hsD : (below (s.gpr .rsp) 24).Disjoint ⟨D, n⟩)
    (hsB : (below (s.gpr .rsp) 24).Disjoint ⟨B, 320⟩)
    (hc : Covers ([] ++ [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩, below (s.gpr .rsp) 24] s.mem s'.mem →
      bytesAt s'.mem D n = List.zipWith (· ^^^ ·) (bytesAt s.mem D n) (keystream (stateAt s.mem S) n) → Q s') :
    WP isa v.callee.inPlace s Q := by
  obtain hn' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  have hd := v.depth_le
  obtain h8 : Region.Sub (below (s.gpr .rsp) 8) (below (s.gpr .rsp) 24) := below_sub (by lit_omega) (by lit_omega)
  have hk := v.stack_le
  obtain hk' : Region.Sub ⟨s.gpr .rsp - 8 - BitVec.ofNat 64 v.stack, v.stack⟩ (below (s.gpr .rsp) 24) := by
    rw [show s.gpr .rsp - 8 - BitVec.ofNat 64 v.stack = s.gpr .rsp - BitVec.ofNat 64 (8 + v.stack) by
      rw [BitVec.sub_sub, BitVec.ofNat_add]; rfl]
    exact Offset.sub_below _ (by lit_omega) (by lit_omega)
  obtain hpre : (xorStack v.stack).pre (s.callEntry.withRegions [] [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩]) := by
    simp only [xorStack, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp), hrdi, hrsi, hrdx, hrcx, hn']
    exact ⟨trivial, trivial, hSD, hSB, hDB, hsS.sub_left h8, hsD.sub_left h8, hsB.sub_left h8,
      hsS.sub_left hk', hsD.sub_left hk', hsB.sub_left hk', hwrap⟩
  refine v.wpIn hpre hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost, _⟩
  obtain hf' : Frame [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩, below (s.gpr .rsp) 24] s.mem s'.mem := by
    refine hf.sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨below (s.gpr .rsp) 24, by simp, below_sub (by lit_omega) (by lit_omega)⟩
  refine hQ s' hrd hwr hcs hf' ?_
  simp only [xorX86_64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), hrdi, hrsi, hrdx, hn', hm₂] at hpost
  rw [hpost, bytesAt_frame (callEntry_frame s) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hsD.sub_left h8).symm) (by lit_omega),
    Xor.stateAt_frame (callEntry_frame s) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hsS.sub_left h8).symm)]

/-- The output, pointwise the input XORed with `ks`. -/
theorem bytesAt_xor {m m' : Mem} {D : Addr} {n : Nat} {ks : List Byte} (hks : ks.length = n)
    (h : ∀ k < n, m' (D + BitVec.ofNat 64 k) = m (D + BitVec.ofNat 64 k) ^^^ ks.getD k 0) :
    bytesAt m' D n = List.zipWith (· ^^^ ·) (bytesAt m D n) ks := by
  apply List.ext_getElem
  · simp [bytesAt, hks]
  · intro k h₁ h₂
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_zipWith]
    rw [h k h₁, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega_arith), Option.getD_some]

theorem ret_stk24 (s₀ : State) : (sret s₀).Disjoint (sstk s₀) := by
  have := Offset.disjoint_base (s₀.gpr .rsp - BitVec.ofNat 64 24) (d := 24) (n := 8) (k := 24) (by decide) (by decide)
  rwa [BitVec.sub_add_cancel] at this

theorem tailCall_ok {s₀ : State} (hp : APre s₀) {C t : Nat} (hC : C ≤ 1024 * t) (ht : sL s₀ - 1024 * t < 1024)
    {s : State} (h : SInv s₀ C t s) :
    WP isa (.seq (.block [.mov .r8 (.reg .rsi)]) (.call "vg_chacha20_xor_avx512" xor)) s fun s' => gprPreserved s₀ s' ∧ xorSplitX86_64.post s₀ s' := by
  obtain hL := sL_lt s₀
  have hle := h.le
  obtain hsp : s.gpr .rsp = s₀.gpr .rsp := h.keep .rsp (by simp [calleeSaved])
  obtain hw' : 1024 * t + (sL s₀ - 1024 * t) ≤ sL s₀ := by omega_arith
  obtain sD : Region.Sub ⟨sdp s₀ + BitVec.ofNat 64 (1024 * t), sL s₀ - 1024 * t⟩ (sdR s₀) :=
    Offset.sub_base _ hw'
  show WP isa XorImpl.avx512.callee.inPlace s _
  refine xor_call XorImpl.avx512 h.rdi h.rsi h.rdx h.rcx (by omega_arith) (hp.st_d.sub_right sD) hp.st_b (hp.d_b.sub_left sD)
    (by have := hp.wrap_d; bv_omega) (by rw [hsp]; exact hp.stk_st) (by rw [hsp]; exact hp.stk_d.sub_right sD)
    (by rw [hsp]; exact hp.stk_b)
    (by
      rw [h.rd, h.wr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨stR s₀, by simp, 0, by simp, show 0 + 64 ≤ 64 by omega_arith⟩
      · exact ⟨sdR s₀, by simp, 1024 * t, rfl, hw'⟩
      · exact ⟨bufR s₀, by simp, 0, by simp, show 0 + 320 ≤ 320 by omega_arith⟩)
    (by
      rw [h.wr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨stR s₀, by simp, 0, by simp, show 0 + 64 ≤ 64 by omega_arith⟩
      · exact ⟨sdR s₀, by simp, 1024 * t, rfl, hw'⟩
      · exact ⟨bufR s₀, by simp, 0, by simp, show 0 + 320 ≤ 320 by omega_arith⟩)
    fun s' _ _ hcs hf hpost => ?_
  rw [hsp] at hf
  refine post_of_V hp ⟨⟨fun r hr => by rw [hcs r hr, h.keep r hr, V_keep s₀ hr], ?_⟩, ?_⟩
  · show s'.mem.readW (s₀.gpr .rsp) 64 = (vmem s₀).readW (s₀.gpr .rsp) 64
    refine (hf.readW (r := sret s₀) (Region.contains_self _ _) ?_ (by decide)).trans ?_
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hp.ret_st
      · exact hp.ret_d.sub_right sD
      · exact hp.ret_b
      · exact ret_stk24 s₀
    · refine (h.frame.readW (r := sret s₀) (Region.contains_self _ _) ?_ (by decide)).trans ?_
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hp.ret_st
        · exact hp.ret_d
        · exact hp.ret_b
      · exact ((vmem_frame s₀).readW (r := sret s₀) (a := s₀.gpr .rsp) (w := 64) (Region.contains_self _ _)
          (by intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hp.ret_d) (by decide))
  · show bytesAt s'.mem (sdp s₀) (sL s₀) =
      List.zipWith (· ^^^ ·) (bytesAt (vmem s₀) (sdp s₀) (sL s₀)) (keystream (Avx2.S0 (V s₀)) (sL s₀))
    rw [V_S0 hp]
    refine bytesAt_xor (length_keystream _ _) fun k hk => ?_
    rw [vmem_dst s₀ hk]
    by_cases hk' : k < 1024 * t
    · have n_w : ¬ (⟨sdp s₀ + BitVec.ofNat 64 (1024 * t), sL s₀ - 1024 * t⟩ : Region).Contains
          (sdp s₀ + BitVec.ofNat 64 k) 1 := by
        simp only [Region.Contains]; bv_omega
      rw [hf _ (by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact fun hc => hp.st_d _ hc (Avx2.in_dR (s₀ := V s₀) hk)
          · exact n_w
          · exact fun hc => hp.d_b _ (Avx2.in_dR (s₀ := V s₀) hk) hc
          · exact fun hc => hp.stk_d _ hc (Avx2.in_dR (s₀ := V s₀) hk)), h.done k hk']
    · have ea : sdp s₀ + BitVec.ofNat 64 k =
          sdp s₀ + BitVec.ofNat 64 (1024 * t) + BitVec.ofNat 64 (k - 1024 * t) := by
        rw [add_ofNat, Nat.add_sub_cancel' (by omega_arith)]
      obtain x := Avx2.bytes_of_bytesAt (length_keystream _ _) hpost (k := k - 1024 * t) (by omega_arith)
      rw [← ea, h.cnt, keystream_getD _ (by omega_arith), Avx2.ctr_ctr] at x
      rw [x, h.todo k hk (by omega_arith) (by omega_arith), keystream_getD _ hk,
        show 16 * t + (k - 1024 * t) / 64 = k / 64 by omega_arith, show (k - 1024 * t) % 64 = k % 64 by omega_arith]

theorem rest_ok {s₀ : State} (hp : APre s₀) {t : Nat} (ht : sL s₀ - 1024 * t < 1024) {s : State}
    (h : SInv s₀ (Cof s₀) t s) :
    WP isa (.seq (.block [.alu .cmp .rdx (.imm 513)]) (.ite .b (.seq (.block [.mov .r8 (.reg .rsi)]) (.call "vg_chacha20_xor_avx512" xor)) last16Sel)) s
      fun s' => gprPreserved s₀ s' ∧ xorSplitX86_64.post s₀ s' := by
  obtain hL := sL_lt s₀
  have hle := h.le
  refine WP.seq (WP.mono (Avx512.cmp513_ok s) fun s₁ ⟨g₁, m₁, rd₁, wr₁, c₁⟩ => ?_)
  obtain h₁ := h.of_eq g₁ m₁ rd₁ wr₁
  obtain hr : (s.gpr .rdx).toNat = sL s₀ - 1024 * t := by rw [h.rdx, toNat_ofNat_lt (by omega_arith)]
  refine WP.ite (decide (sL s₀ - 1024 * t < 513)) (by simp [eval, c₁, hr]) (fun hs => ?_) (fun hs => ?_)
  · simp only [decide_eq_true_eq] at hs
    obtain hC : Cof s₀ ≤ 1024 * t := by
      have := Cof_le (s₀ := s₀) (by omega_arith); omega_arith
    exact tailCall_ok hp hC ht h₁
  · simp only [decide_eq_false_iff_not] at hs
    exact WP.mono (last16Sel_ok hp (Cof_ok hp) (by omega_arith) ht h₁) fun s' ⟨hg, hpost, _⟩ =>
      post_of_V hp ⟨hg, hpost⟩

/-! ## The whole function -/

theorem xorSplit_eq : xorSplit =
    .seq entryC (.seq (.block copyArgs) (.seq (Impl.ChaCha20Poly1305.X86_64.SealGather.copyBytes .z64)
    (.seq (.block (loopArgs ++ Impl.ChaCha20.X86_64.Avx512Tail.consts ++ consts ++
      ([.alu .cmp .rdx (.imm 1024)] : List Instr)))
    (.seq (.ite .b (.block []) (.loop bodySel .ae))
    (.seq (.block [.alu .cmp .rdx (.imm 513)]) (.ite .b (.seq (.block [.mov .r8 (.reg .rsi)]) (.call "vg_chacha20_xor_avx512" xor)) last16Sel)))))) := rfl

theorem correct {s₀ : State} (hp : APre s₀) :
    WP isa xorSplit s₀ fun s' => gprPreserved s₀ s' ∧ xorSplitX86_64.post s₀ s' := by
  rw [xorSplit_eq]
  refine prologue_ok hp fun s₁ h₁ hc => ?_
  exact WP.seq (WP.mono (loop_ok hp (Cof_ok hp) h₁ hc) fun s₂ ⟨t, ht, h₂⟩ => rest_ok hp ht h₂)

end VG.Proof.ChaCha20.X86_64.Avx512Split

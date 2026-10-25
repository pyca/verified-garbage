module

public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512Tail.Sym
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.SymSel
import VerifiedGarbage.Proof.Framework.Block

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
  ⟨fun r p hp => (hz r p).trans (h.reg r p hp), fun b i hb hi => by rw [hm]; exact h.mem b i hb hi,
    hg.trans h.gpr, hr.trans h.rd, hw.trans h.wr, hm ▸ h.frame, fun hd => hm.trans (h.clean hd)⟩

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
  refine WP.seq (WP.mono (cmpR10_ok s (c := off + 64) (by omega)) fun s₁ ⟨g₁, m₁, rd₁, wr₁, z₁, c₁⟩ => ?_)
  have h₁ : SRel D σ s₀ s₁ := h.congr z₁ m₁ g₁ rd₁ wr₁
  have ea : ∀ r, s₁.ea (at_ r off) = s₀.gpr r + BitVec.ofNat 64 off := fun r => by
    simp only [State.ea, at_, g₁, h.gpr]
    exact congrArg _ (ofInt_ofNat off)
  have rest : ∀ s₂ : State, SRel D (σ.setReg (xidx t) fun p => .inp (off / 4 + p)) s₀ s₂ →
      WP isa (.block [z .vpxord t t x, .vmovdqu32Store (at_ .rsi off) t]) s₂ (SRel D σ' s₀) :=
    fun s₂ h₂ => srun_ok hc _ h₂ e
  refine WP.ite (decide ((s₀.gpr .r10).toNat < off + 64)) (by simp [eval, c₁, h.gpr]) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    have i2 : InRegions (s₁.rd ++ s₁.wr) ((regn D s₀ 2).base + BitVec.ofNat 64 (4 * (off / 4))) (4 * 16) :=
      in_regn' hc (b := 2) (by decide) (wr₁.trans h.wr) (by simp only [bsize]; omega) (by decide)
    have ea2 : s₁.ea (at_ .rsi off) = (regn D s₀ 2).base + BitVec.ofNat 64 (4 * (off / 4)) := by
      rw [ea]; simp only [regn, baseR]; congr 2; omega
    obtain ⟨s₂, hx, h₂⟩ := h₁.load t (at_ .rsi off) (f := fun p => .inp (off / 4 + p)) (by rw [ea2]; exact i2)
      (fun p hp => by
        rw [ea2, add_ofNat', ← Nat.mul_add, h₁.mem 2 _ (by decide) (by simp only [bsize]; omega), hcl p hp]
        simp only [T.eval, inpW, inp_block hoff hp, regn, baseR]
        rw [ite_eq_right (by omega)])
    exact WP.block_cons_iff.2 ⟨s₂, hx, rest s₂ h₂⟩
  · simp only [decide_eq_false_iff_not, Nat.not_lt] at hb
    have cs : (srcR s₀).Contains (s₀.gpr .r8 + BitVec.ofNat 64 off) 64 := by
      simp only [srcR, Region.Contains]
      rw [show s₀.gpr .r8 + BitVec.ofNat 64 off - s₀.gpr .r8 = BitVec.ofNat 64 off by bv_omega_arith,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    obtain ⟨s₂, hx, h₂⟩ := h₁.load t (at_ .r8 off) (f := fun p => .inp (off / 4 + p))
      (by rw [ea, rd₁, wr₁, h.rd, h.wr]; exact hs.r _ _ (by decide) cs)
      (fun p hp => by
        have cp : (srcR s₀).Contains (s₀.gpr .r8 + BitVec.ofNat 64 off + BitVec.ofNat 64 (4 * p)) (32 / 8) := by
          simp only [srcR, Region.Contains] at cs ⊢
          rw [show s₀.gpr .r8 + BitVec.ofNat 64 off + BitVec.ofNat 64 (4 * p) - s₀.gpr .r8 =
            BitVec.ofNat 64 (off + 4 * p) by rw [add_ofNat']; bv_omega_arith,
            BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          rw [show s₀.gpr .r8 + BitVec.ofNat 64 off - s₀.gpr .r8 = BitVec.ofNat 64 off by bv_omega_arith,
            BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at cs
          omega
        rw [ea, m₁, h.frame.readW cp hs.d (by decide)]
        simp only [T.eval, inpW, inp_block hoff hp]
        rw [ite_eq_left (by omega), add_ofNat', show off + 4 * p = 4 * (off / 4 + p) by omega])
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

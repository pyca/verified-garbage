module

public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Sym
public import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx512Split
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# ChaCha20 on x86-64 with AVX-512: blocks of the input from either buffer

`vg_chacha20_xor_split`'s pass loads each block of its input from `src` or
from the data (`selXor`), by a comparison of `r10` with the block's end: a
branch on lengths. `Sym.sel` runs both branches at once, loading the block
as the terms `T.inp`, which stand for the doublewords the branch taken
loads (`inpW`), and `sel_ok` proves either branch agrees: from the data, a
block not yet written (so still that of the pass's start); from `src`, the
first `r10` bytes (at most 1024) at `r8`, which are readable and apart from
what the pass writes (`SelOk`). `Sym.runPieces` runs `pieces`.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Avx512

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx512
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.ChaCha20 (Word)

/-- `XOR` of the keystream in `x` into the input's block at offset `off`
(loaded as `T.inp`, through `t`), stored to the data: if the block is in the
pass, and the data's block not yet written. -/
def Sym.sel (σ : Sym) (x t : XReg) (off : Nat) : Option Sym :=
  if off % 64 = 0 ∧ off + 64 ≤ 1024 ∧
      (List.range 16).all (fun p => σ.mem 2 (off / 4 + p) == .mem 2 (off / 4 + p)) then
    (σ.setReg (xidx t) fun p => .inp (off / 4 + p)).run [z .vpxord t t x, .vmovdqu32Store (at_ .rsi off) t]
  else none

def Sym.runPieces (σ : Sym) : List Piece → Option Sym
  | [] => some σ
  | .ins is :: ps => (σ.run is).bind fun σ' => σ'.runPieces ps
  | .sel x t off :: ps => (σ.sel x t off).bind fun σ' => σ'.runPieces ps

/-- The bytes of `src` the pass may load: the first `r10` at `r8`, at most
1024. -/
def srcR (s₀ : State) : Region := ⟨s₀.gpr .r8, min (s₀.gpr .r10).toNat 1024⟩

/-- They may be read, and the pass does not write them. -/
structure SelOk (s₀ : State) : Prop where
  r : ∀ a n, 0 < n → (srcR s₀).Contains a n → InRegions (s₀.rd ++ s₀.wr) a n
  d : ∀ r ∈ wregs s₀, (srcR s₀).Disjoint r

theorem SRel.congr {σ : Sym} {s₀ s s' : State} (h : SRel σ s₀ s) (hz : ∀ r p, zw s' r p = zw s r p)
    (hm : s'.mem = s.mem) (hg : s'.gpr = s.gpr) (hr : s'.rd = s.rd) (hw : s'.wr = s.wr) : SRel σ s₀ s' :=
  ⟨fun r p hp => (hz r p).trans (h.reg r p hp), fun b i hb hi => by rw [hm]; exact h.mem b i hb hi,
    hg.trans h.gpr, hr.trans h.rd, hw.trans h.wr, hm ▸ h.frame, fun hd => hm.trans (h.clean hd)⟩

/-- A load of 64 bytes whose doublewords are given terms. -/
theorem SRel.load {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) (d : XReg) (m : MemOp) {f : Nat → T}
    (hin : InRegions (s.rd ++ s.wr) (s.ea m) 64)
    (hv : ∀ p < 16, s.mem.readW (s.ea m + BitVec.ofNat 64 (4 * p)) 32 = (f p).eval s₀) :
    ∃ s', exec (.vmovdqu32Load d m) s = some s' ∧ SRel (σ.setReg (xidx d) f) s₀ s' := by
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

theorem signExtend_ofNat {c : Nat} (hc : c < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.ofNat 32 c) = BitVec.ofNat 64 c := by
  have hm : (BitVec.ofNat 32 c).msb = false := by
    rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; simp; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt (show c < 2 ^ 32 by omega), Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega)]

set_option simprocs false in
/-- `cmp r10, c`. -/
theorem cmpR10_ok (s : State) {c : Nat} (hc : c < 2 ^ 31) :
    WP isa (.block [.alu .cmp .r10 (.imm (BitVec.ofNat 32 c))]) s fun s' =>
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r p, zw s' r p = zw s r p) ∧
      s'.cf = some (decide ((s.gpr .r10).toNat < c)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left', signExtend_ofNat hc]
  refine ⟨trivial, trivial, trivial, trivial, fun _ _ => rfl, ?_⟩
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem inp_block {off p : Nat} (hoff : off % 64 = 0) (hp : p < 16) : (off / 4 + p) / 16 = off / 64 := by
  omega

theorem sel_ok {s₀ : State} (hc : Ctx s₀) (hs : SelOk s₀) {σ σ' : Sym} {s : State} (h : SRel σ s₀ s)
    {x t : XReg} {off : Nat} (e : σ.sel x t off = some σ') :
    WP isa (selXor x t off) s (SRel σ' s₀) := by
  unfold Sym.sel at e
  split at e
  case isFalse => cases e
  rename_i hcond
  obtain ⟨hoff, hlim, hcl⟩ := hcond
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hcl
  refine WP.seq (WP.mono (cmpR10_ok s (c := off + 64) (by omega)) fun s₁ ⟨g₁, m₁, rd₁, wr₁, z₁, c₁⟩ => ?_)
  have h₁ : SRel σ s₀ s₁ := h.congr z₁ m₁ g₁ rd₁ wr₁
  have r10 : s₁.gpr .r10 = s₀.gpr .r10 := by rw [g₁, h.gpr]
  have ea : ∀ r, s₁.ea (at_ r off) = s₀.gpr r + BitVec.ofNat 64 off := fun r => by
    simp only [State.ea, at_, g₁, h.gpr]
    exact congrArg _ (ofInt_ofNat off)
  -- The rest of the block, from the loaded block on.
  have rest : ∀ s₂ : State, SRel (σ.setReg (xidx t) fun p => .inp (off / 4 + p)) s₀ s₂ →
      WP isa (.block [z .vpxord t t x, .vmovdqu32Store (at_ .rsi off) t]) s₂ (SRel σ' s₀) :=
    fun s₂ h₂ => srun_ok hc _ h₂ e
  refine WP.ite (decide ((s₀.gpr .r10).toNat < off + 64)) (by simp [eval, c₁, h.gpr]) (fun hb => ?_) (fun hb => ?_)
  · -- From the data.
    simp only [decide_eq_true_eq] at hb
    have i2 : InRegions (s₁.rd ++ s₁.wr) ((regn s₀ 2).base + BitVec.ofNat 64 (4 * (off / 4))) (4 * 16) :=
      in_regn' hc (b := 2) (by decide) (wr₁.trans h.wr) (by simp only [bsize]; omega)
    have ea2 : s₁.ea (at_ .rsi off) = (regn s₀ 2).base + BitVec.ofNat 64 (4 * (off / 4)) := by
      rw [ea]; simp only [regn, baseR]; congr 2; omega
    obtain ⟨s₂, hx, h₂⟩ := h₁.load t (at_ .rsi off) (f := fun p => .inp (off / 4 + p)) (by rw [ea2]; exact i2)
      (fun p hp => by
        rw [ea2, add_ofNat', ← Nat.mul_add, h₁.mem 2 _ (by decide) (by simp only [bsize]; omega), hcl p hp]
        simp only [T.eval, inpW, inp_block hoff hp, regn, baseR]
        rw [ite_eq_right (by omega)])
    exact WP.block_cons_iff.2 ⟨s₂, hx, rest s₂ h₂⟩
  · -- From `src`.
    simp only [decide_eq_false_iff_not, Nat.not_lt] at hb
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
theorem runPieces_ok {s₀ : State} (hc : Ctx s₀) (hs : SelOk s₀) :
    ∀ (ps : List Piece) {σ σ' : Sym} {s : State}, SRel σ s₀ s → σ.runPieces ps = some σ' →
      WP isa (pieces ps) s (SRel σ' s₀)
  | [], _, _, _, h, e => by cases e; exact WP.block_nil h
  | .ins is :: ps, _, _, _, h, e => by
    simp only [Sym.runPieces, Option.bind_eq_some_iff] at e
    obtain ⟨σ₁, e₁, e₂⟩ := e
    show WP isa (.seq (.block is) (pieces ps)) _ _
    exact WP.seq (WP.mono (srun_ok hc is h e₁) fun s₁ h₁ => runPieces_ok hc hs ps h₁ e₂)
  | .sel x t off :: ps, _, _, _, h, e => by
    simp only [Sym.runPieces, Option.bind_eq_some_iff] at e
    obtain ⟨σ₁, e₁, e₂⟩ := e
    show WP isa (.seq (selXor x t off) (pieces ps)) _ _
    exact WP.seq (WP.mono (sel_ok hc hs h e₁) fun s₁ h₁ => runPieces_ok hc hs ps h₁ e₂)

end VG.Proof.ChaCha20.X86_64.Avx512

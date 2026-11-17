module

public import VerifiedGarbage.Proof.RsaKeyGen.Hdr
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
public import VerifiedGarbage.Impl.RsaKeyGen.X86_64.Candidate
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Bignum.X86_64.R2
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.RsaKeyGen.CandMath
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdE
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.Octets
import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Push
import Mathlib.Algebra.NeZero
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
import VerifiedGarbage.Proof.RsaKeyGen.Bits
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
public import VerifiedGarbage.Spec.RsaKeyGen
import Mathlib.Algebra.GroupWithZero.Basic
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrRoundAll
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop
public import VerifiedGarbage.Proof.RsaKeyGen.Generate
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrShift
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrMain
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.X86_64.Call

/-! ### `RsaKeyGen.X86_64.KTail`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86_64.KEnd`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86_64.Fin`, which only this module used -/

section

/-!
# A candidate on x86-64: zeros to `out`, and the ends

`zeroOut_ok`: zeros to the `out_len` octets of `out`; `finish_ok`: `rax` to
`used`, the status returned and the saved registers restored, for `finNone`,
`finUsed` and `finPrime` (`c` to `out` first).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64
open VG.WriteBytes (writeW8_apply)

/-- `zeroOut`: `k` zeros to `out`. -/
theorem zeroOut_ok {s : State} {B : Addr} {Z k : Nat} {op : Addr} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hZ : 8 * 32 ≤ Z) (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31)
    (hO : word s.mem B (8 * kOut) = op) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 k)
    (hout : ∀ j < k, InRegions s.wr (op + BitVec.ofNat 64 j) 1) :
    WP isa zeroOut s fun t => (∀ i < k, t.mem (op + BitVec.ofNat 64 i) = 0) ∧
      (∀ x, (∀ i < k, x ≠ op + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧ Keep [.rsi, .rcx, .rax] s t := by
  have hn := hs.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega_using [hZ, hi])
  unfold zeroOut
  refine WP.seq (WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun t => t.gpr .rsi = op ∧
      t.gpr .rcx = BitVec.ofNat 64 k ∧ t.gpr .rax = 0 ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hdi, hdrOff, hl kOut (by decide), hl kLen (by decide), hO, hK]) rfl)
    fun s₁ ⟨⟨hsi, hcx, hax, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (wp_upto (a := 0) (N := k) (by omega_using [hk1]) (FailInv s₁ op k) ?_ (fun t h => h)
    ⟨Keep.refl _ _, by rw [hsi, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero], by rw [hcx, Nat.sub_zero],
      fun i hi => absurd hi (by omega_using []), fun x _ => rfl⟩) fun t hI => ⟨hI.bytes, fun x hx => by
        rw [hI.frame x hx, hm₁], ((k₁.trans hI.keep).mono (by decide))⟩
  intro j _ hj t hI
  have hst : InRegions t.wr (op + BitVec.ofNat 64 j) 1 := by
    rw [hI.keep.2.2, k₁.2.2]; exact hout j hj
  have hax' : (t.gpr .rax).setWidth 8 = 0 := by rw [hI.keep.gpr (by decide), hax]; rfl
  refine WP.mono (WP.keep [.rsi, .rcx] (Q := fun t' =>
      t'.mem = t.mem.writeW (op + BitVec.ofNat 64 j) (0 : BitVec 8) ∧
      t'.gpr .rsi = op + BitVec.ofNat 64 (j + 1) ∧ t'.gpr .rcx = BitVec.ofNat 64 (k - (j + 1)) ∧
      t'.zf = some (decide (j + 1 = k))) (by
    xrun [State.ea, at0, hI.rsi, hI.rcx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hst, hax',
      ofNat64_pred (show 1 ≤ k - j by omega_using [hj]) (by omega_using [hk']), BitVec.add_assoc, ofNat_add_one,
      ofNat64_beq_zero (show k - j - 1 < 2 ^ 64 by omega_using [hk'])]
    exact ⟨by rw [show k - j - 1 = k - (j + 1) by omega_using []], decide_eq_decide.mpr (by omega_using [hj])⟩) rfl)
    fun t' ⟨⟨hm, hsi', hcx', hz⟩, k'⟩ => ⟨hz, (hI.keep.trans k').mono (by decide), hsi', hcx', ?_, ?_⟩
  · intro i hi
    rw [hm, writeW8_apply]
    by_cases hij : i = j
    · subst hij; simp
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega_using [hk', hj, hi]) (by omega_using [hk', hj]) hij))]
      exact hI.bytes i (by omega_using [hi, hij])
  · intro x hx
    rw [hm, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega_using [])))]
    exact hI.frame x fun i hi => hx i (by omega_using [hi])

/-- What an end leaves: the status `st` returned, `u` at `used`, the saved
registers restored, and memory outside the scratch space and `used`
unchanged. -/
structure FinPost (s t : State) (B : Addr) (Z : Nat) (up : Addr) (st u : Nat) : Prop where
  rax : t.gpr .rax = BitVec.ofNat 64 st
  used : t.mem.readW up 64 = BitVec.ofNat 64 u
  saved : ∀ i < 6, t.gpr (saved.getD i .rax) = word s.mem B (8 * i)
  frame : ∀ x, Z ≤ ofs B x → (∀ b < 8, x ≠ up + BitVec.ofNat 64 b) → t.mem x = s.mem x
  keep : Keep mmRegs s t

theorem addr_of_sub (x up : Addr) : x = up + BitVec.ofNat 64 (x - up).toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]

/-- The 8 octets at `up`, outside the scratch space, do not meet its header. -/
theorem up_sep {B up : Addr} {Z : Nat} (hn : B.toNat + Z ≤ 2 ^ 64) (hZ : 8 * 32 ≤ Z)
    (hupZ : ∀ b < 8, Z ≤ ofs B (up + BitVec.ofNat 64 b)) {i : Nat} (hi : i < 32) :
    Mem.Sep (off B (8 * i)) (64 / 8) up (64 / 8) := by
  intro x h1 h2
  have e1 := addr_of_sub x (off B (8 * i))
  have e2 := addr_of_sub x up
  have := hupZ _ h2
  rw [← e2, e1, ofs_off B (by omega_arith)] at this
  omega_arith

theorem finish_eq (st : Nat) : finish st = [.mov .rdx (.mem (hdr kUsedP)), .store (at0 .rdx) .rax,
    .mov32 .rax (.imm (BitVec.ofNat 32 st)), .mov .rbx (.mem (hdr 0)), .mov .rbp (.mem (hdr 1)),
    .mov .r12 (.mem (hdr 2)), .mov .r13 (.mem (hdr 3)), .mov .r14 (.mem (hdr 4)), .mov .r15 (.mem (hdr 5))] := rfl

/-- `finish st` with `u` in `rax`. -/
theorem finish_ok {s : State} {B : Addr} {Z : Nat} {up : Addr} {st u : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hZ : 8 * 32 ≤ Z) (hst : st < 2 ^ 31) (hax : s.gpr .rax = BitVec.ofNat 64 u)
    (hU : word s.mem B (8 * kUsedP) = up) (hupw : InRegions s.wr up 8)
    (hupZ : ∀ b < 8, Z ≤ ofs B (up + BitVec.ofNat 64 b)) :
    WP isa (.block (finish st)) s (FinPost s · B Z up st u) := by
  have hn := hs.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega_using [hZ, hi])
  have hw : ∀ i < 32, ∀ v : BitVec 64, word (s.mem.writeW up v) B (8 * i) = word s.mem B (8 * i) := fun i hi v =>
    Mem.readW_writeW_sep (up_sep hn hZ hupZ hi) (by decide)
  refine WP.mono (WP.keep [.rdx, .rax, .rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun t =>
      t.gpr .rax = BitVec.ofNat 64 st ∧ t.mem = s.mem.writeW up (BitVec.ofNat 64 u) ∧
      t.gpr .rbx = word s.mem B (8 * 0) ∧ t.gpr .rbp = word s.mem B (8 * 1) ∧ t.gpr .r12 = word s.mem B (8 * 2) ∧
      t.gpr .r13 = word s.mem B (8 * 3) ∧ t.gpr .r14 = word s.mem B (8 * 4) ∧ t.gpr .r15 = word s.mem B (8 * 5)) (by
    rw [finish_eq]
    xrun [State.ea, hdr, at0, hdi, hdrOff, hl kUsedP (by decide), hU, show BitVec.ofInt 64 0 = 0#64 from rfl,
      BitVec.add_zero, hupw, hax, hl 0 (by decide), hl 1 (by decide), hl 2 (by decide), hl 3 (by decide),
      hl 4 (by decide), hl 5 (by decide), hw 0 (by decide), hw 1 (by decide), hw 2 (by decide), hw 3 (by decide),
      hw 4 (by decide), hw 5 (by decide)]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using []),
      Nat.mod_eq_of_lt (by omega_using [hst]), Nat.mod_eq_of_lt (by omega_using [hst])]) rfl) fun t ⟨⟨hax', hm, h0, h1, h2, h3, h4, h5⟩, k⟩ => ⟨hax', ?_, ?_, ?_, k.mono (by decide)⟩
  · rw [hm]; exact Mem.readW_writeW_self64 _ _ _
  · intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_using [hi]) with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  · intro x _ hx
    rw [hm]
    refine Mem.write_apply fun h => hx _ h ?_
    exact addr_of_sub x up

/-- `finNone`: 0 to `used`, status 0. -/
theorem finNone_ok {s : State} {B : Addr} {Z : Nat} {up : Addr} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hZ : 8 * 32 ≤ Z) (hU : word s.mem B (8 * kUsedP) = up) (hupw : InRegions s.wr up 8)
    (hupZ : ∀ b < 8, Z ≤ ofs B (up + BitVec.ofNat 64 b)) :
    WP isa finNone s (FinPost s · B Z up 0 0) := by
  unfold finNone
  rw [show ∀ l : List Instr, [Instr.mov32 .rax (.imm 0)] ++ l = [.mov32 .rax (.imm 0)] ++ l from fun _ => rfl,
    WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 0 ∧ t.mem = s.mem) (by xrun) rfl)
    fun s₁ ⟨⟨hax, hm₁⟩, k₁⟩ => ?_
  refine WP.mono (finish_ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans hdi) hZ (by decide) hax
    (by rw [hm₁]; exact hU) (by rw [k₁.2.2]; exact hupw) hupZ) fun t h => ?_
  exact ⟨h.rax, h.used, fun i hi => (h.saved i hi).trans (by rw [hm₁]), fun x hx hx' => (h.frame x hx hx').trans
    (by rw [hm₁]), (k₁.trans h.keep).mono (by decide)⟩

/-- `finUsed st`: `kUsed` to `used`, status `st`. -/
theorem finUsed_ok {s : State} {B : Addr} {Z : Nat} {up : Addr} {st u : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hZ : 8 * 32 ≤ Z) (hst : st < 2 ^ 31) (hu : word s.mem B (8 * kUsed) = BitVec.ofNat 64 u)
    (hU : word s.mem B (8 * kUsedP) = up) (hupw : InRegions s.wr up 8)
    (hupZ : ∀ b < 8, Z ≤ ofs B (up + BitVec.ofNat 64 b)) :
    WP isa (finUsed st) s (FinPost s · B Z up st u) := by
  have hn := hs.nowrap
  unfold finUsed
  rw [show ∀ l : List Instr, [Instr.mov .rax (.mem (hdr kUsed))] ++ l = [.mov .rax (.mem (hdr kUsed))] ++ l
    from fun _ => rfl, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 u ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hdi, hdrOff, hs.ld (d := 8 * kUsed) (by unfold kUsed sFn; omega_using [hZ]), hu]) rfl)
    fun s₁ ⟨⟨hax, hm₁⟩, k₁⟩ => ?_
  refine WP.mono (finish_ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans hdi) hZ hst hax
    (by rw [hm₁]; exact hU) (by rw [k₁.2.2]; exact hupw) hupZ) fun t h => ?_
  exact ⟨h.rax, h.used, fun i hi => (h.saved i hi).trans (by rw [hm₁]), fun x hx hx' => (h.frame x hx hx').trans
    (by rw [hm₁]), (k₁.trans h.keep).mono (by decide)⟩

theorem exit_eq : [Instr.mov32 .rax (.imm 1)] ++ exit = [.mov32 .rax (.imm 1),
    .mov .rbx (.mem (hdr 0)), .mov .rbp (.mem (hdr 1)), .mov .r12 (.mem (hdr 2)), .mov .r13 (.mem (hdr 3)),
    .mov .r14 (.mem (hdr 4)), .mov .r15 (.mem (hdr 5))] := rfl

theorem sxm1'' : BitVec.signExtend 64 (BitVec.ofInt 32 (-1)) = mask true := by decide

/-- `finPrime`: `c` (`aN`) to the `8 w` octets of `out`, `kUsed` to `used`,
status 1. -/
theorem finPrime_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {op up : Addr} {u : Nat}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 27)
    (hu : word s.mem B (8 * kUsed) = BitVec.ofNat 64 u) (hO : word s.mem B (8 * kOut) = op)
    (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hU : word s.mem B (8 * kUsedP) = up) (hupw : InRegions s.wr up 8)
    (hupZ : ∀ b < 8, Z ≤ ofs B (up + BitVec.ofNat 64 b))
    (hout : ∀ j < 8 * w, InRegions s.wr (op + BitVec.ofNat 64 j) 1)
    (hsep : ∀ j < 8 * w, Z ≤ ofs B (op + BitVec.ofNat 64 j))
    (hou : ∀ j < 8 * w, ∀ b < 8, op + BitVec.ofNat 64 j ≠ up + BitVec.ofNat 64 b) :
    WP isa finPrime s fun t =>
      (List.range (8 * w)).map (fun i => t.mem (op + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (wv s.mem B (slot w aN) w) (8 * w) ∧
      t.gpr .rax = BitVec.ofNat 64 1 ∧ t.mem.readW up 64 = BitVec.ofNat 64 u ∧
      (∀ i < 6, t.gpr (saved.getD i .rax) = word s.mem B (8 * i)) ∧
      (∀ x, Z ≤ ofs B x → (∀ b < 8, x ≠ up + BitVec.ofNat 64 b) → (∀ j < 8 * w, x ≠ op + BitVec.ofNat 64 j) →
        t.mem x = s.mem x) ∧ Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega_using [hZ, this])
  have sN := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  have hw8 : w = (8 * w + 7) / 8 := by omega_using []
  have hZ8 : 8 * 32 ≤ Z := by have := hdr_lt_slot w 8 (show 31 < 32 by decide); omega_using [hZ, this]
  -- `used`, and the arguments of `storeBE`.
  unfold finPrime
  refine WP.seq (WP.mono (WP.keep [.rax, .rdx, .rbx, .rsi, .rcx, .r15] (Q := fun t => t.gpr .rbx = off B (slot w aN) ∧
      t.gpr .rsi = op ∧ t.gpr .rcx = BitVec.ofNat 64 (8 * w) ∧ t.gpr .r15 = mask true ∧
      t.mem = s.mem.writeW up (BitVec.ofNat 64 u)) (by
    xrun [State.ea, hdr, at0, hg.rdi, hdrOff, hl kUsed (by decide), hl kUsedP (by decide), hu, hU,
      show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hupw, hl (sArr aN) (by decide), hl kOut (by decide),
      hl kLen (by decide), hg.hdr.harr aN (by decide), hO, hK, sxm1'']) rfl) fun s₁ ⟨⟨hbx, hsi, hcx, h15, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hg.scr.congr k₁.2.2
  have hZx₁ : ∀ x, ofs B x < Z → s₁.mem x = s.mem x := fun x hx => by
    rw [hm₁]; refine Mem.write_apply fun h => ?_
    have := hupZ _ h
    rw [← addr_of_sub x up] at this; omega_using [hx, this]
  have hwv₁ : wv s₁.mem B (slot w aN) w = wv s.mem B (slot w aN) w :=
    wv_congr fun i hi => Mem.readW_congr fun b hb => hZx₁ _ (by rw [ofs_off B (by omega_using [hn, sN, hi, hb])]; omega_using [sN, hi, hb])
  refine WP.seq (WP.mono (storeBE_ok hs₁ hbx hsi hcx h15 (by omega_using [hw]) (by omega_using [hw']) hw8 (by omega_using [sN])
    (fun j hj => by rw [k₁.2.2]; exact hout j hj) hsep) fun s₂ ⟨hb₂, hf₂, hwr₂, hrd₂, k₂⟩ => ?_)
  simp only [↓reduceIte] at hb₂
  have hZx : ∀ x, ofs B x < Z → s₂.mem x = s.mem x := fun x hx =>
    (hf₂ x fun j hj he => by have := hsep j hj; rw [← he] at this; omega_using [hx, this]).trans (hZx₁ x hx)
  have hw₂ : ∀ d, d + 8 ≤ Z → word s₂.mem B d = word s.mem B d := fun d hd =>
    Mem.readW_congr fun b hb => hZx _ (by rw [ofs_off B (by omega_using [hn, hd, hb])]; omega_using [hd, hb])
  have hs₂ : Scr s₂ B Z := ⟨by rw [hwr₂, k₁.2.2]; exact hg.scr.1, hn⟩
  have hdi₂ : s₂.gpr .rdi = B := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hg.rdi)
  have hl₂ : ∀ i < 32, InRegions (s₂.rd ++ s₂.wr) (off B (8 * i)) 8 := fun i hi =>
    hs₂.ld (by have := hdr_lt_slot w 8 hi; omega_using [hZ8, hi])
  -- Status 1, and the saved registers.
  refine WP.mono (WP.keep [.rax, .rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun t =>
      t.gpr .rax = BitVec.ofNat 64 1 ∧ t.mem = s₂.mem ∧
      t.gpr .rbx = word s₂.mem B (8 * 0) ∧ t.gpr .rbp = word s₂.mem B (8 * 1) ∧ t.gpr .r12 = word s₂.mem B (8 * 2) ∧
      t.gpr .r13 = word s₂.mem B (8 * 3) ∧ t.gpr .r14 = word s₂.mem B (8 * 4) ∧ t.gpr .r15 = word s₂.mem B (8 * 5)) (by
    rw [exit_eq]
    xrun [State.ea, hdr, hdi₂, hdrOff, hl₂ 0 (by decide), hl₂ 1 (by decide), hl₂ 2 (by decide), hl₂ 3 (by decide),
      hl₂ 4 (by decide), hl₂ 5 (by decide)]) rfl) fun t ⟨⟨hax, hm, h0, h1, h2, h3, h4, h5⟩, k⟩ => ⟨?_, hax, ?_, fun i hi => ?_, fun x hx hx' hx'' => ?_,
      ((k₁.trans k₂).trans k).mono (by decide)⟩
  · rw [hm, ← hwv₁, ← hb₂]
  · rw [hm]
    refine (Mem.readW_congr fun b hb => hf₂ _ fun j hj he => hou j hj b hb he.symm).trans ?_
    rw [hm₁]; exact Mem.readW_writeW_self64 _ _ _
  · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_using [hi]) with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0.trans (hw₂ _ (by omega_using [hZ8]))
    · exact h1.trans (hw₂ _ (by omega_using [hZ8]))
    · exact h2.trans (hw₂ _ (by omega_using [hZ8]))
    · exact h3.trans (hw₂ _ (by omega_using [hZ8]))
    · exact h4.trans (hw₂ _ (by omega_using [hZ8]))
    · exact h5.trans (hw₂ _ (by omega_using [hZ8]))
  · rw [hm, hf₂ x hx'', hm₁]
    exact Mem.write_apply fun h => hx' _ h (addr_of_sub x up)

end VG.Proof.RsaKeyGen.X86_64

end

end


/-!
# A candidate on x86-64: how it ends

`KEnd`: the status, `used`, `out` (the prime, or unchanged), the saved
registers restored and memory outside the scratch space, `out` and `used`
unchanged. `finUsed_end` and `finNone_end`: the ends that leave `out`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- The octets of `out`. -/
abbrev outBytes (m : Mem) (op : Addr) (k : Nat) : List Byte := (List.range k).map fun i => m (op + BitVec.ofNat 64 i)

/-- How a candidate ends, from `s`: status `st`, `u` to `used`, and `out`
the `k` octets of `c` if `outv = some c`, else unchanged. -/
structure KEnd (s t : State) (B : Addr) (Z : Nat) (op up : Addr) (k st u : Nat) (outv : Option Nat) : Prop where
  rax : t.gpr .rax = BitVec.ofNat 64 st
  used : t.mem.readW up 64 = BitVec.ofNat 64 u
  out : outBytes t.mem op k = match outv with
    | some c => Spec.Rsa.i2osp c k
    | none => outBytes s.mem op k
  saved : ∀ i < 6, t.gpr (saved.getD i .rax) = word s.mem B (8 * i)
  frame : ∀ x, Z ≤ ofs B x → (∀ b < 8, x ≠ up + BitVec.ofNat 64 b) → (∀ j < k, x ≠ op + BitVec.ofNat 64 j) →
    t.mem x = s.mem x
  keep : Keep mmRegs s t

/-- The facts about `out` and `used` every end needs. -/
structure OutUp (s : State) (B : Addr) (Z : Nat) (op up : Addr) (k : Nat) : Prop where
  upw : InRegions s.wr up 8
  upZ : ∀ b < 8, Z ≤ ofs B (up + BitVec.ofNat 64 b)
  outw : ∀ j < k, InRegions s.wr (op + BitVec.ofNat 64 j) 1
  outZ : ∀ j < k, Z ≤ ofs B (op + BitVec.ofNat 64 j)
  ou : ∀ j < k, ∀ b < 8, op + BitVec.ofNat 64 j ≠ up + BitVec.ofNat 64 b

theorem OutUp.congr {s t : State} {B : Addr} {Z : Nat} {op up : Addr} {k : Nat} (h : OutUp s B Z op up k)
    (hw : t.wr = s.wr) : OutUp t B Z op up k :=
  ⟨by rw [hw]; exact h.upw, h.upZ, fun j hj => by rw [hw]; exact h.outw j hj, h.outZ, h.ou⟩

theorem KEnd.of_fin {s t : State} {B : Addr} {Z : Nat} {op up : Addr} {k st u : Nat} (ho : OutUp s B Z op up k)
    (h : FinPost s t B Z up st u) : KEnd s t B Z op up k st u none :=
  ⟨h.rax, h.used, List.map_congr_left fun i hi => h.frame _ (ho.outZ i (List.mem_range.mp hi))
    fun b hb => ho.ou i (List.mem_range.mp hi) b hb, h.saved, fun x hx hx' _ => h.frame x hx hx', h.keep⟩

/-- `KEnd` from a state with the same memory below `Z` and the same
registers but `mmRegs`. -/
theorem KEnd.trans_pre {s₀ s t : State} {B : Addr} {Z : Nat} {op up : Addr} {k st u : Nat} {outv : Option Nat}
    (h : KEnd s t B Z op up k st u outv) (hlo : ∀ i < 6, word s.mem B (8 * i) = word s₀.mem B (8 * i))
    (hhi : ∀ x, Z ≤ ofs B x → s.mem x = s₀.mem x) (k₀ : Keep mmRegs s₀ s)
    (hoZ : ∀ j < k, Z ≤ ofs B (op + BitVec.ofNat 64 j)) :
    KEnd s₀ t B Z op up k st u outv := by
  refine ⟨h.rax, h.used, ?_, fun i hi => (h.saved i hi).trans (hlo i hi), fun x hx hx' hx'' =>
    (h.frame x hx hx' hx'').trans (hhi x hx), (k₀.trans h.keep).mono (by decide)⟩
  rw [h.out]
  cases outv
  · exact List.map_congr_left fun i hi => hhi _ (hoZ i (List.mem_range.mp hi))
  · rfl

end VG.Proof.RsaKeyGen.X86_64

end

end

/-!
# A candidate on x86-64: Montgomery setup, Miller–Rabin and the result

`mrResult_ok`: the end from `kStat`, as the primality test's result ends a
candidate (`TestEnd`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- How a primality test's result ends a candidate `c`. -/
def TestEnd (s t : State) (B : Addr) (Z : Nat) (op up : Addr) (k : Nat) (r : List Byte) (c : Nat) :
    Option (Bool × List Byte) → Prop
  | none => KEnd s t B Z op up k 0 0 none
  | some (true, rest) => KEnd s t B Z op up k 1 (r.length - rest.length) (some c)
  | some (false, rest) => KEnd s t B Z op up k 3 (r.length - rest.length) none

/-- `mrResult`, after Miller–Rabin ended with `res`. -/
theorem mrResult_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c : Nat} {op up : Addr} {r : List Byte}
    {res : Option (Bool × List Byte)} (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 27)
    (hn : wv s.mem B (slot w aN) w = c) (ho : OutUp s B Z op up (8 * w))
    (hO : word s.mem B (8 * kOut) = op) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hU : word s.mem B (8 * kUsedP) = up)
    (h0 : res = none → word s.mem B (8 * kStat) = BitVec.ofNat 64 0)
    (h1 : ∀ b rest, res = some (b, rest) → word s.mem B (8 * kStat) = BitVec.ofNat 64 (if b then 1 else 3) ∧
      word s.mem B (8 * kUsed) = BitVec.ofNat 64 (r.length - rest.length)) :
    WP isa mrResult s fun t => TestEnd s t B Z op up (8 * w) r c res := by
  have hn' := hg.scr.nowrap
  have h8 : 8 * 32 ≤ Z := by have := hdr_lt_slot w 8 (show 31 < 32 by decide); omega_arith
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * kStat)) 8 :=
    hg.scr.ld (by have := hdr_lt_slot w 8 (show kStat < 32 by decide); omega_arith)
  unfold mrResult
  rcases hres : res with _ | ⟨b, rest⟩
  · have hS := h0 hres
    refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some true ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, hg.rdi, hdrOff, hl, hS]) rfl) fun s₁ ⟨⟨hz, hm⟩, k₁⟩ => ?_)
    refine WP.ite true (by simp [eval, hz]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine WP.mono (finNone_ok (hg.scr.congr k₁.2.2) ((k₁.gpr (by decide)).trans hg.rdi) h8 (by rw [hm]; exact hU)
      (by rw [k₁.2.2]; exact ho.upw) ho.upZ) fun t h => ?_
    exact (KEnd.of_fin (ho.congr k₁.2.2) h).trans_pre (fun i _ => by rw [hm]) (fun x _ => by rw [hm])
      (k₁.mono (by decide)) ho.outZ
  · obtain ⟨hS, hu⟩ := h1 b rest hres
    have hv : (if b then 1 else 3 : Nat) < 2 ^ 63 := by cases b <;> decide
    refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some false ∧
        t.gpr .rax = BitVec.ofNat 64 (if b then 1 else 3) ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, hg.rdi, hdrOff, hl, hS, BitVec.and_self]; cases b <;> decide) rfl)
      fun s₁ ⟨⟨hz, hax₁, hm⟩, k₁⟩ => ?_)
    refine WP.ite false (by simp [eval, hz]) (fun h => absurd h (by decide)) (fun _ => ?_)
    refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some b ∧ t.mem = s.mem) (by
      xrun [hax₁, hm]; cases b <;> decide) rfl) fun s₂ ⟨⟨hz₂, hm₂⟩, k₂⟩ => ?_)
    have hs₂ := (hg.scr.congr k₁.2.2).congr k₂.2.2
    have hdi₂ : s₂.gpr .rdi = B := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hg.rdi)
    have ho₂ := (ho.congr k₁.2.2).congr k₂.2.2
    have k12 : Keep mmRegs s s₂ := (k₁.trans k₂).mono (by decide)
    refine WP.ite b (by simp [eval, hz₂]) (fun hb => ?_) (fun hb => ?_)
    · subst hb
      have hg₂ : Good s₂ B Z w mi := ⟨hs₂, hdi₂, by rw [hm₂]; exact hg.hdr⟩
      refine WP.mono (finPrime_ok (u := r.length - rest.length) hg₂ hZ hw hw' (by rw [hm₂]; exact hu) (by rw [hm₂]; exact hO)
        (by rw [hm₂]; exact hK) (by rw [hm₂]; exact hU) ho₂.upw ho₂.upZ ho₂.outw ho₂.outZ ho₂.ou)
        fun t ⟨hb, hax, hus, hsv, hfr, k⟩ => ?_
      refine ⟨hax, hus, by rw [hm₂, hn] at hb; exact hb, fun i hi => by rw [hsv i hi, hm₂],
        fun x hx hx' hx'' => by rw [hfr x hx hx' hx'', hm₂], (k12.trans k).mono (by decide)⟩
    · subst hb
      refine WP.mono (finUsed_ok (u := r.length - rest.length) hs₂ hdi₂ h8 (by decide) (by rw [hm₂]; exact hu) (by rw [hm₂]; exact hU)
        ho₂.upw ho₂.upZ) fun t h => ?_
      exact (KEnd.of_fin ho₂ h).trans_pre (fun i _ => by rw [hm₂]) (fun x _ => by rw [hm₂]) k12 ho.outZ

end VG.Proof.RsaKeyGen.X86_64

end

end

/-! ### `RsaKeyGen.X86_64.Close`, which only this module used -/

section

/-!
# A candidate on x86-64: too close to `p`

`closeCheck` loads `p` into `aX`, puts `c − p` (with its borrow) in `aAcc`
(`diff_ok`), negates it under the mask of the borrow (`neg_ok`): `|c − p|`;
then compares the bound `2^(64 w − 100)` (`aTmp`, by `setWord`) with it
(`cmpLoop_ok`), and leaves the mask of `|c − p| ≤ 2^(64 w − 100)`, or 0
without `p`, in `rbp` (`closeCheck_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- After `j` words of the negation: the low `j` words negated if `b`, with
the carry in `rbp`. -/
structure NegInv (s₀ : State) (B : Addr) (Z e : Nat) (b : Bool) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rbp, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : Outside B e (8 * j) s₀.mem t.mem
  val : ∃ c : Bool, t.gpr .rbp = mask c ∧
    wv t.mem B e j + 2 ^ (64 * j) * c.toNat =
      if b then 2 ^ (64 * j) - wv s₀.mem B e j else wv s₀.mem B e j

theorem xor_mask_toNat (x : BitVec 64) (b : Bool) :
    (x ^^^ mask b).toNat = if b then 2 ^ 64 - 1 - x.toNat else x.toNat := by
  cases b
  · simp [mask_false]
  · simp only [mask_true, BitVec.xor_allOnes, BitVec.toNat_not, ite_true]

theorem negStep_ok {s₀ : State} {B : Addr} {Z w e : Nat} {b : Bool}
    (hsi : s₀.gpr .rsi = off B e) (h15 : s₀.gpr .r15 = mask b) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (hw : w < 2 ^ 32) (he : e + 8 * w ≤ Z) {j : Nat} (hj : j < w) {t : State} (hI : NegInv s₀ B Z e b j t) :
    WP isa (.block (([.mov .rax (.mem (ix .rsi .r14)), .alu .xor .rax (.reg .r15), cfFromRbp, .alu .adc .rax (.imm 0),
        .store (ix .rsi .r14) .rax, cfToRbp] : List Instr) ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ NegInv s₀ B Z e b (j + 1) t' := by
  have hn := hI.scr.nowrap
  obtain tsi : t.gpr .rsi = off B e := (hI.keep.gpr (by decide)).trans hsi
  obtain t15 : t.gpr .r15 = mask b := (hI.keep.gpr (by decide)).trans h15
  obtain t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  obtain ⟨c, hbp, hval⟩ := hI.val
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t₁ =>
      ∃ c' : Bool, t₁.gpr .rbp = mask c' ∧ ∃ r : BitVec 64, t₁.mem = t.mem.writeW (off B (e + 8 * j)) r ∧
        r.toNat + 2 ^ 64 * c'.toNat = (word t.mem B (e + 8 * j) ^^^ mask b).toNat + c.toNat) ?_ rfl)
    fun t₁ ⟨⟨c', h₁, r, hm, hr⟩, k₁⟩ => ?_
  · unfold cfFromRbp cfToRbp
    xrun [State.ea, ix, addr0 tsi hI.r14, t15, hbp, cf_mask, hI.scr.ld (show e + 8 * j + 8 ≤ Z by omega_using [he, hj]),
      hI.scr.st (show e + 8 * j + 8 ≤ Z by omega_using [he, hj])]
    refine ⟨_, rfl, _, rfl, ?_⟩
    have := adc_toNat (word t.mem B (e + 8 * j) ^^^ mask b) (BitVec.signExtend 64 (0 : BitVec 32)) c
    rw [show (BitVec.signExtend 64 (0 : BitVec 32)).toNat = 0 from rfl, Nat.add_zero] at this
    exact this
  obtain t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  obtain t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega_arith) (by omega_using [he, hn])) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  obtain hx : word t.mem B (e + 8 * j) = word s₀.mem B (e + 8 * j) := hI.out.word (by omega_using []) (by omega_using [he, hj, hn])
  rw [hx, xor_mask_toNat] at hr
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14, ?_,
    ⟨c', (k'.gpr (by decide)).trans h₁, ?_⟩⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B r (by omega_using [he, hj, hn]) x (by omega_using [hx'])]
    exact hI.out x (by omega_using [hx'])
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega_using [he, hj, hn])]
    simp only [wv]
    obtain hD := wv_lt s₀.mem B e j
    obtain hxl := (word s₀.mem B (e + 8 * j)).isLt
    obtain hc1 := Bool.toNat_le c
    obtain hc1' := Bool.toNat_le c'
    rw [pow64_succ]
    generalize 2 ^ (64 * j) = P at hD hval ⊢
    generalize wv s₀.mem B e j = D at hD hval ⊢
    generalize (word s₀.mem B (e + 8 * j)).toNat = x at hxl hr ⊢
    generalize wv t.mem B e j = V at hval ⊢
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte] at hr hval ⊢
      grind
    · simp only [↓reduceIte] at hr hval ⊢
      obtain hPx : P * x + P ≤ P * 2 ^ 64 := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hxl
      obtain e1 : P * r.toNat + P * 2 ^ 64 * c'.toNat = P * (2 ^ 64 - 1 - x + c.toNat) := by
        rw [Nat.mul_assoc, ← Nat.mul_add, hr]
      obtain e2 : P * (2 ^ 64 - 1 - x + c.toNat) + P * x + P = P * 2 ^ 64 + P * c.toNat := by
        rw [← Nat.mul_add, ← Nat.mul_succ, ← Nat.mul_add]; congr 1; omega_using [hxl]
      omega_using [hD, hval, e1, e2]

/-- `diffLoop`: `[aAcc] := c − p` (`aN` minus `aX`), its borrow's mask in `rbp`. -/
theorem diff_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) :
    WP isa (seqs diffLoop) s fun t => ∃ b : Bool, t.gpr .rbp = mask b ∧
      wv t.mem B (slot w aAcc) w + wv s.mem B (slot w aX) w = wv s.mem B (slot w aN) w + 2 ^ (64 * w) * b.toNat ∧
      Outside B (slot w aAcc) (8 * w) s.mem t.mem ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧
      Keep [.rax, .rbp, .rsi, .r8, .r10, .r12, .r14] s t := by
  have hn := hg.scr.nowrap
  obtain hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega_using [hZ, this])
  obtain sN := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  obtain sX := Nat.le_trans (slot_le (w := w) (show aX < 8 by decide)) hZ
  obtain sA := Nat.le_trans (slot_le (w := w) (show aAcc < 8 by decide)) hZ
  obtain p1 := slot_sep (w := w) (show aAcc ≠ aN by decide)
  obtain p2 := slot_sep (w := w) (show aAcc ≠ aX by decide)
  unfold diffLoop
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.r12, .r8, .r10, .rsi, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .r8 = off B (slot w aN) ∧ t.gpr .r10 = off B (slot w aX) ∧ t.gpr .rsi = off B (slot w aAcc) ∧
      t.gpr .rbp = mask false ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl (sArr aN) (by decide), hl (sArr aX) (by decide),
      hl (sArr aAcc) (by decide), hg.hdr.hw, hg.hdr.harr aN (by decide), hg.hdr.harr aX (by decide),
      hg.hdr.harr aAcc (by decide)]) rfl) fun s₁ ⟨⟨h12, h8, h10, hsi, hbp, hm₁⟩, k₁⟩ => ?_)
  obtain hs₁ := hg.scr.congr k₁.2.2
  refine WP.mono (wordLoop_ok (start := 0) (N := w) (by omega_using [hw]) hw' (SubInv s₁ B Z (slot w aN) (slot w aX) (slot w aAcc))
    (fun t h14 hm k _ => ⟨hs₁.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      ⟨false, by rw [k.gpr (by decide)]; exact hbp, by simp [wv]⟩⟩)
    (fun j _ hj t hI => subStep_ok h8 h10 hsi h12 (by omega_using [hw']) (by omega_using [sN]) (by omega_using [sX])
        (by omega_using [sA]) (by omega_using [p1]) (by omega_using [p2]) hj hI))
    fun t hI => ?_
  obtain ⟨b, hb, hv⟩ := hI.val
  rw [hm₁] at hv
  refine ⟨b, hb, hv, by rw [← hm₁]; exact hI.out, (hI.keep.gpr (by decide)).trans h12, (k₁.trans hI.keep).mono (by decide)⟩

/-- `negLoop`: `[aAcc]` negated modulo `2^(64 w)` if `rbp` is the mask of
`true`. -/
theorem neg_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) {b : Bool} (hbp : s.gpr .rbp = mask b) (h12 : s.gpr .r12 = BitVec.ofNat 64 w) :
    WP isa (seqs negLoop) s fun t =>
      wv t.mem B (slot w aAcc) w = (if b then 2 ^ (64 * w) - wv s.mem B (slot w aAcc) w else wv s.mem B (slot w aAcc) w)
        % 2 ^ (64 * w) ∧
      Outside B (slot w aAcc) (8 * w) s.mem t.mem ∧ Keep [.rax, .rbp, .rsi, .r14, .r15] s t := by
  have hn := hg.scr.nowrap
  obtain hl : InRegions (s.rd ++ s.wr) (off B (8 * sArr aAcc)) 8 :=
    hg.scr.ld (by have := hdr_lt_slot w 8 (show sArr aAcc < 32 by decide); omega_using [hZ, this])
  obtain sA := Nat.le_trans (slot_le (w := w) (show aAcc < 8 by decide)) hZ
  unfold negLoop
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.r15, .rsi] (Q := fun t => t.gpr .r15 = mask b ∧ t.gpr .rsi = off B (slot w aAcc) ∧
      t.mem = s.mem) (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl, hbp, hg.hdr.harr aAcc (by decide)]) rfl)
    fun s₁ ⟨⟨h15, hsi, hm₁⟩, k₁⟩ => ?_)
  obtain hs₁ := hg.scr.congr k₁.2.2
  refine WP.mono (wordLoop_ok (start := 0) (N := w) (by omega_using [hw]) hw' (NegInv s₁ B Z (slot w aAcc) b)
    (fun t h14 hm k _ => ⟨hs₁.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      ⟨b, by rw [k.gpr (by decide), k₁.gpr (by decide)]; exact hbp, by cases b <;> simp [wv]⟩⟩)
    (fun j _ hj t hI => negStep_ok hsi h15 ((k₁.gpr (by decide)).trans h12) (by omega_using [hw']) (by omega_using [sA]) hj hI))
    fun t hI => ?_
  obtain ⟨c, _, hv⟩ := hI.val
  rw [hm₁] at hv
  refine ⟨?_, by rw [← hm₁]; exact hI.out, (k₁.trans hI.keep).mono (by decide)⟩
  obtain hlt := wv_lt t.mem B (slot w aAcc) w
  rw [← hv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- What `closeCheck` changes: `aX`, `aAcc` and `aTmp`. -/
def closeRanges (w : Nat) : List (Nat × Nat) :=
  [(slot w aX, 8 * (w + 2)), (slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2))]

/-- `closeRanges`'s ranges, in the header and in the arrays. -/
theorem closeRanges_shape (w : Nat) : VG.Proof.RsaKeyGen.RangeShape w []
    [(1, 1), (2, 1), (3, 1)] (closeRanges w) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false,
    closeRanges, Public.aX, Public.aAcc, Public.aTmp, aX, aAcc, aTmp] at hr
  rcases hr with rfl | rfl | rfl
  · exact .inr ⟨(1, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(2, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(3, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩

theorem sxm1 : BitVec.signExtend 64 (BitVec.ofInt 32 (-1)) = BitVec.allOnes 64 := by decide

theorem mask_not (b : Bool) : mask b ^^^ BitVec.allOnes 64 = mask (!b) := by cases b <;> decide

/-- The bound: `[aTmp] := 2^(64 w − 100)`, `aTmp`'s word `w − 2` set to `2^28`. -/
theorem bound_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z)
    (hw : 4 ≤ w) (hw' : w < 2 ^ 31) :
    WP isa (.seq (.block [.mov .r12 (.mem (hdr sW)), .mov .rcx (.reg .r12), .alu .sub .rcx (.imm 2),
        .mov32 .rdx (.imm (BitVec.ofNat 32 (2 ^ 28)))]) (setWord aTmp .rcx)) s fun t =>
      wv t.mem B (slot w aTmp) w = 2 ^ (64 * w - 100) ∧ Outside B (slot w aTmp) (8 * (w + 2)) s.mem t.mem ∧
      Keep [.rax, .rcx, .rdx, .r8, .r12, .r14] s t := by
  have hn := hg.scr.nowrap
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * sW)) 8 := hg.scr.ld
      (by have := hdr_lt_slot w 8 (show sW < 32 by decide); omega_using [hZ, this])
  refine WP.seq (WP.mono (WP.keep [.r12, .rcx, .rdx] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rcx = BitVec.ofNat 64 (w - 2) ∧ (t.gpr .rdx).toNat = 2 ^ 28 ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl, hg.hdr.hw, sx2]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (2 : BitVec 64).toNat = 2 from rfl]
    omega_using [hw]) rfl)
    fun s₁ ⟨⟨h12, hcx, hdx, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (setWord_ok (hg.scr.congr k₁.2.2) ((k₁.gpr (by decide)).trans hg.rdi) (by rw [hm₁]; exact hg.hdr) hZ h12
    (by omega_using [hw]) hw' (o := aTmp) (by decide) (ri := .rcx) (by decide) (i := w - 2) (by omega_using [hw]) hcx)
    fun t ⟨hv, ho, k⟩ => ⟨?_, by rw [hm₁] at ho; exact ho, (k₁.trans k).mono (by decide)⟩
  rw [hv, hdx, ← Nat.pow_add]; congr 1; omega_using [hw]

/-- `closeCheck` with `p` (`8 w` octets `pB`): `rbp` the mask of
`|c − p| ≤ 2^(64 w − 100)`. -/
theorem closeInner_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z)
    (hw : 4 ≤ w) (hw' : w ≤ 64) {pP : Addr} {pB : List Byte} (hP : word s.mem B (8 * kP) = pP)
    (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w)) (hpl : pB.length = 8 * w) (hsrc : Src s B Z pP pB) :
    WP isa (seqs (([.block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr kP)), .mov .rcx (.mem (hdr kLen)),
        .mov .rbx (.mem (hdr (sArr aX)))], loadBE] : List (Prog isa)) ++ diffLoop ++ negLoop ++ ([
      .block [.mov .r12 (.mem (hdr sW)), .mov .rcx (.reg .r12), .alu .sub .rcx (.imm 2),
        .mov32 .rdx (.imm (BitVec.ofNat 32 (2 ^ 28)))],
      setWord aTmp .rcx,
      .block [.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aTmp))), .mov .r10 (.mem (hdr (sArr aAcc))),
        .mov32 .rbp (.imm 0)],
      wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)), cfToRbp],
      .block [.alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))]] : List (Prog isa)))) s fun t =>
      t.gpr .rbp = mask (decide (Spec.RsaKeyGen.absDiff (wv s.mem B (slot w aN) w) (Spec.Rsa.os2ip pB) ≤
        2 ^ (64 * w - 100))) ∧
      Good t B Z w minv ∧ Frm B (closeRanges w) s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r10, .r12, .r14, .r15] s t := by
  have hn := hg.scr.nowrap
  obtain hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega_using [hZ, this])
  obtain hw8 : (8 * w + 7) / 8 = w := by omega_using []
  obtain sN := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  obtain sX := Nat.le_trans (slot_le (w := w) (show aX < 8 by decide)) hZ
  obtain sA := Nat.le_trans (slot_le (w := w) (show aAcc < 8 by decide)) hZ
  obtain sT := Nat.le_trans (slot_le (w := w) (show aTmp < 8 by decide)) hZ
  obtain hsl : ∀ r ∈ closeRanges w, r.1 + r.2 ≤ Z := by
    simp only [closeRanges, List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl | rfl) <;> omega_using [sX, sA, sT]
  obtain hdisj : ∀ j < 8, j ≠ aX → j ≠ aAcc → j ≠ aTmp → ∀ r ∈ closeRanges w,
      slot w j + 8 * (w + 2) ≤ r.1 ∨ r.1 + r.2 ≤ slot w j := by
    intro j hj h1 h2 h3 r hr
    simp only [closeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact slot_sep h1
    · exact slot_sep h2
    · exact slot_sep h3
  obtain hhd : ∀ i < 32, ∀ r ∈ closeRanges w, 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i := by
    intro i hi r hr
    simp only [closeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Or.inl (hdr_lt_slot w _ hi)
  refine wp_seqs_append (by simp) (by simp) ?_
  refine wp_seqs_append (by simp) (by simp [negLoop]) ?_
  refine wp_seqs_append (by simp) (by simp [diffLoop]) ?_
  simp only [seqs]
  -- `p` into `aX`.
  refine WP.seq (WP.mono (WP.keep [.r12, .rsi, .rcx, .rbx] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rsi = pP ∧ t.gpr .rcx = BitVec.ofNat 64 (8 * w) ∧ t.gpr .rbx = off B (slot w aX) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl kP (by decide), hl kLen (by decide),
      hl (sArr aX) (by decide), hg.hdr.hw, hP, hK, hg.hdr.harr aX (by decide)]) rfl)
    fun s₁ ⟨⟨h12₁, hsi₁, hcx₁, hbx₁, hm₁⟩, k₁⟩ => ?_)
  obtain hs₁ := hg.scr.congr k₁.2.2
  refine WP.mono (loadArr_ok (j := aX) hs₁ (by decide) (by rw [hw8]; exact hZ)
    (hsrc.congrK (by rw [hm₁]; exact InScr.refl _ _ _) k₁) hpl (by omega_using [hw]) (by omega_using [hw']) hsi₁ hcx₁
    (by rw [hw8]; exact hbx₁)) fun s₂ ⟨hp₂, ha₂, k₂⟩ => ?_
  rw [hw8] at hp₂ ha₂
  obtain hf₂ : Frm B (closeRanges w) s.mem s₂.mem := by
    rw [← hm₁]; exact Frm.of_arrays ha₂ fun _ hj => (List.mem_singleton.mp hj) ▸ by simp [closeRanges]
  obtain hg₂ : Good s₂ B Z w minv := ⟨hs₁.congr k₂.2.2, (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hg.rdi),
    ha₂.hdr (by rw [hm₁]; exact hg.hdr)⟩
  obtain hc₂ : wv s₂.mem B (slot w aN) w = wv s.mem B (slot w aN) w :=
    hf₂.wv_eq (fun r hr => by have := hdisj aN (by decide) (by decide) (by decide) (by decide) r hr; omega_using [this])
        (by omega_using [hn, sN])
  -- `c − p`.
  refine WP.mono (diff_ok hg₂ hZ (by omega_using [hw]) (by omega_using [hw'])) fun s₃ ⟨b, hb₃, hv₃, ho₃, h12₃, k₃⟩ => ?_
  rw [hc₂, hp₂] at hv₃
  obtain hf₃ : Frm B (closeRanges w) s.mem s₃.mem :=
    hf₂.trans (Frm.of_outside (ho₃.mono (o' := slot w aAcc) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_using []))
        (by simp [closeRanges]))
  obtain hg₃ : Good s₃ B Z w minv := ⟨hg₂.scr.congr k₃.2.2, (k₃.gpr (by decide)).trans hg₂.rdi,
    Hdr.outside hg₂.hdr ho₃ (by unfold slot; omega_using [])⟩
  -- `|c − p|`.
  refine WP.mono (neg_ok hg₃ hZ (by omega_using [hw]) (by omega_using [hw']) hb₃ h12₃) fun s₄ ⟨hv₄, ho₄, k₄⟩ => ?_
  obtain hD := wv_lt s₃.mem B (slot w aAcc) w
  obtain habs : wv s₄.mem B (slot w aAcc) w = Spec.RsaKeyGen.absDiff (wv s.mem B (slot w aN) w) (Spec.Rsa.os2ip pB) := by
    rw [hv₄, absDiff_of hv₃ hD]
    exact Nat.mod_eq_of_lt (by
      unfold Spec.RsaKeyGen.absDiff
      have := wv_lt s.mem B (slot w aN) w
      have : Spec.Rsa.os2ip pB < 2 ^ (64 * w) := by
        have := os2ip_lt pB; rw [hpl, pow256_eq] at this; rwa [show 8 * (8 * w) = 64 * w by omega_using []] at this
      split <;> omega_arith)
  obtain hf₄ : Frm B (closeRanges w) s.mem s₄.mem :=
    hf₃.trans (Frm.of_outside (ho₄.mono (o' := slot w aAcc) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_using []))
        (by simp [closeRanges]))
  obtain hg₄ : Good s₄ B Z w minv := ⟨hg₃.scr.congr k₄.2.2, (k₄.gpr (by decide)).trans hg₃.rdi,
    Hdr.outside hg₃.hdr ho₄ (by unfold slot; omega_using [])⟩
  -- The bound.
  refine WP.assoc (WP.seq (WP.mono (bound_ok hg₄ hZ hw (by omega_using [hw'])) fun s₅ ⟨hT₅, ho₅, k₅⟩ => ?_))
  obtain hf₅ : Frm B (closeRanges w) s.mem s₅.mem := hf₄.trans (Frm.of_outside ho₅ (by simp [closeRanges]))
  obtain hg₅ : Good s₅ B Z w minv := ⟨hg₄.scr.congr k₅.2.2, (k₅.gpr (by decide)).trans hg₄.rdi,
    Hdr.outside hg₄.hdr ho₅ (by unfold slot; omega_using [])⟩
  obtain hA₅ : wv s₅.mem B (slot w aAcc) w = Spec.RsaKeyGen.absDiff (wv s.mem B (slot w aN) w) (Spec.Rsa.os2ip pB) := by
    rw [ho₅.wv (k := w) (by have := slot_sep (w := w) (show aTmp ≠ aAcc by decide); omega_using [this])
        (by omega_using [hn, sA])]; exact habs
  obtain hl₅ : ∀ i < 32, InRegions (s₅.rd ++ s₅.wr) (off B (8 * i)) 8 := fun i hi =>
    hg₅.scr.ld (by have := hdr_lt_slot w 8 hi; omega_using [hZ, this])
  refine WP.seq (WP.mono (WP.keep [.r12, .rbx, .r10, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rbx = off B (slot w aTmp) ∧ t.gpr .r10 = off B (slot w aAcc) ∧ t.gpr .rbp = mask false ∧ t.mem = s₅.mem) (by
    xrun [State.ea, hdr, hg₅.rdi, hdrOff, hl₅ sW (by decide), hl₅ (sArr aTmp) (by decide), hl₅ (sArr aAcc) (by decide),
      hg₅.hdr.hw, hg₅.hdr.harr aTmp (by decide), hg₅.hdr.harr aAcc (by decide)]) rfl)
    fun s₆ ⟨⟨h12₆, hbx₆, h10₆, hbp₆, hm₆⟩, k₆⟩ => ?_)
  refine WP.seq (WP.mono (cmpLoop_ok (hg₅.scr.congr k₆.2.2) hbx₆ h10₆ h12₆ hbp₆ (by omega_using [hw])
      (by omega_using [hw']) (by omega_using [sT])
    (by omega_using [sA])) fun s₇ ⟨hbp₇, hm₇, k₇⟩ => ?_)
  rw [hm₆, hT₅, hA₅] at hbp₇
  refine WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = mask (!decide (2 ^ (64 * w - 100) <
      Spec.RsaKeyGen.absDiff (wv s.mem B (slot w aN) w) (Spec.Rsa.os2ip pB))) ∧ t.mem = s₇.mem) (by
    xrun [sxm1, hbp₇, mask_not]) rfl) fun t ⟨⟨hbp, hm⟩, k⟩ => ⟨?_, ⟨hg₅.scr.congr (k.2.2.trans (k₇.2.2.trans k₆.2.2)),
      (k.gpr (by decide)).trans ((k₇.gpr (by decide)).trans ((k₆.gpr (by decide)).trans hg₅.rdi)),
      by rw [hm, hm₇, hm₆]; exact hg₅.hdr⟩, by rw [hm, hm₇, hm₆]; exact hf₅,
      (((((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).trans k).mono (by decide)⟩
  rw [hbp, ← decide_not]; simp only [Nat.not_lt]

theorem mask_beq_zero (b : Bool) : (mask b &&& mask b == (0 : BitVec 64)) = !b := by cases b <;> decide

/-- `closeCheck`: ZF set unless the candidate is too close to `p` (none if
`p_len = 0`). -/
theorem closeCheck_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z)
    (hw : 4 ≤ w) (hw' : w ≤ 64) {pP : Addr} {pB : List Byte} (hP : word s.mem B (8 * kP) = pP)
    (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hPl : word s.mem B (8 * kPlen) = BitVec.ofNat 64 pB.length) (hpl : pB.length = 0 ∨ pB.length = 8 * w)
    (hsrc : Src s B Z pP pB) :
    WP isa (seqs closeCheck) s fun t =>
      t.zf = some (!Spec.RsaKeyGen.tooClose (64 * w) (Spec.RsaKeyGen.otherPrime pB) (wv s.mem B (slot w aN) w)) ∧
      Good t B Z w minv ∧ Frm B (closeRanges w) s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r10, .r12, .r14, .r15] s t := by
  obtain hl : InRegions (s.rd ++ s.wr) (off B (8 * kPlen)) 8 :=
    hg.scr.ld (by have := hdr_lt_slot w 8 (show kPlen < 32 by decide); omega_using [hZ, this])
  obtain hlen : pB.length < 2 ^ 64 := by omega_using [hw', hpl]
  unfold closeCheck
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.rax, .rbp] (Q := fun t => t.zf = some (decide (pB = [])) ∧ t.gpr .rbp = mask false ∧
      t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl, hPl]
    cases pB with
    | nil => rfl
    | cons a l =>
      refine beq_false_of_ne fun h => ?_
      have := congrArg BitVec.toNat h
      rw [BitVec.and_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen] at this
      exact absurd this (by simp)) rfl)
    fun s₁ ⟨⟨hz₁, hbp₁, hm₁⟩, k₁⟩ => ?_)
  obtain hg₁ : Good s₁ B Z w minv := ⟨hg.scr.congr k₁.2.2, (k₁.gpr (by decide)).trans hg.rdi, by rw [hm₁]; exact hg.hdr⟩
  obtain fin : ∀ (t : State) (b : Bool), t.gpr .rbp = mask b →
      b = Spec.RsaKeyGen.tooClose (64 * w) (Spec.RsaKeyGen.otherPrime pB) (wv s.mem B (slot w aN) w) →
      Good t B Z w minv → Frm B (closeRanges w) s.mem t.mem →
      Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r10, .r12, .r14, .r15] s t →
      WP isa (.block [.alu .test .rbp (.reg .rbp)]) t fun t' =>
        t'.zf = some (!Spec.RsaKeyGen.tooClose (64 * w) (Spec.RsaKeyGen.otherPrime pB) (wv s.mem B (slot w aN) w)) ∧
        Good t' B Z w minv ∧ Frm B (closeRanges w) s.mem t'.mem ∧
        Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r10, .r12, .r14, .r15] s t' := by
    intro t b hb hbv hgt hf kt
    refine WP.mono (WP.keep [.rbp] (Q := fun t' => t'.zf = some (!b) ∧ t'.mem = t.mem) (by
      xrun [hb, mask_beq_zero]) rfl)
      fun t' ⟨⟨hz, hm⟩, k⟩ => ⟨hbv ▸ hz, ⟨hgt.scr.congr k.2.2, (k.gpr (by decide)).trans hgt.rdi, by rw [hm]; exact hgt.hdr⟩,
        by rw [hm]; exact hf, (kt.trans k).mono (by decide)⟩
  refine WP.seq (WP.ite (!decide (pB = [])) (by simp [eval, hz₁]) (fun he => ?_) (fun he => ?_))
  · simp only [Bool.not_eq_true', decide_eq_false_iff_not] at he
    obtain hpl8 : pB.length = 8 * w := hpl.resolve_left (by rw [List.length_eq_zero_iff]; exact he)
    refine WP.mono (closeInner_ok hg₁ hZ hw hw' (by rw [hm₁]; exact hP) (by rw [hm₁]; exact hK) hpl8
      (hsrc.congrK (by rw [hm₁]; exact InScr.refl _ _ _) k₁)) fun t ⟨hbp, hgt, hf, kt⟩ =>
      fin t _ hbp ?_ hgt (by rw [hm₁] at hf; exact hf) ((k₁.trans kt).mono (by decide))
    simp only [Spec.RsaKeyGen.otherPrime, he, ↓reduceIte, Spec.RsaKeyGen.tooClose, hm₁]
  · simp only [Bool.not_eq_false', decide_eq_true_eq] at he
    refine WP.block_nil (fin s₁ false hbp₁ ?_ hg₁ (by rw [hm₁]; exact Frm.refl _ _ _) (k₁.mono (by decide)))
    simp only [Spec.RsaKeyGen.otherPrime, he, ↓reduceIte, Spec.RsaKeyGen.tooClose]

end VG.Proof.RsaKeyGen.X86_64

end

end

/-! ### `RsaKeyGen.X86_64.LoadC`, which only this module used -/

section

/-!
# A candidate on x86-64: the candidate

`loadC` sets `w = out_len / 8` and the arrays' bases, loads the first
`out_len` octets of `rand` into `aN`, sets its two top bits and its low bit
(`wv_candidate`), and `used := out_len` (`loadC_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- What `loadC` changes. -/
def loadCRanges (w : Nat) : List (Nat × Nat) :=
  [(8 * sW, 8), (8 * sArr 0, 64), (slot w aN, 8 * (w + 2)), (8 * kUsed, 8)]

/-- `loadCRanges`'s ranges, in the header and in the arrays. -/
theorem loadCRanges_shape (w : Nat) : VG.Proof.RsaKeyGen.RangeShape w [(48, 8), (64, 64), (200, 8)]
    [(0, 1)] (loadCRanges w) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false,
    loadCRanges, Public.aN, aN, sFn, sW, sArr, kUsed] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact .inl (by decide)
  · exact .inl (by decide)
  · exact .inr ⟨(0, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inl (by decide)

/-- The head of `loadC`: `w`, the bases, and `rand` and `out_len` into `rsi`
and `rcx`. -/
theorem loadCHead_ok {s : State} {B : Addr} {Z k : Nat} {rp : Addr} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hZ : slot (k / 8) 8 ≤ Z) (hk : k < 2 ^ 31) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 k)
    (hR : word s.mem B (8 * kRand) = rp) :
    WP isa (.block (([.mov .rcx (.mem (hdr kLen)), .mov .r12 (.reg .rcx), .shift .shr .r12 3, .store (hdr sW) .r12] : List Instr) ++
      setBases ++ ([.mov .rsi (.mem (hdr kRand)), .mov .rbx (.mem (hdr (sArr aN)))] : List Instr))) s fun t =>
      t.gpr .rsi = rp ∧ t.gpr .rcx = BitVec.ofNat 64 k ∧ t.gpr .rbx = off B (slot (k / 8) aN) ∧
      word t.mem B (8 * sW) = BitVec.ofNat 64 (k / 8) ∧ (∀ j < 8, word t.mem B (8 * sArr j) = off B (slot (k / 8) j)) ∧
      Frm B [(8 * sW, 8), (8 * sArr 0, 64)] s.mem t.mem ∧ Keep [.rax, .rcx, .rdx, .rbx, .rsi, .r12] s t := by
  have hn := hs.nowrap
  obtain h8 := hdr_lt_slot (k / 8) 0 (show 31 < 32 by decide)
  obtain h0 := slot_le (w := k / 8) (show 0 < 8 by decide)
  obtain hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega_arith)
  obtain hst : InRegions s.wr (off B (8 * sW)) 8 := hs.st (by unfold sW; omega_arith)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rcx, .r12] (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 k ∧
      t.gpr .r12 = BitVec.ofNat 64 (k / 8) ∧ t.mem = s.mem.writeW (off B (8 * sW)) (BitVec.ofNat 64 (k / 8))) (by
    xrun [State.ea, hdr, hdi, hdrOff, hl kLen (by decide), hK, hst]
    have : BitVec.ofNat 64 k >>> 3 = BitVec.ofNat 64 (k / 8) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
        Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt (show k / 8 < 2 ^ 64 by omega_arith)]
    rw [this]; exact ⟨rfl, rfl⟩) rfl) fun t₁ ⟨⟨hcx, h12, hm₁⟩, k₁⟩ => ?_
  refine WP.mono (setBases_ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans hdi) h12 (by unfold sArr; omega_arith))
    fun t₂ ⟨hb₂, ho₂, k₂⟩ => ?_
  obtain hW₂ : word t₂.mem B (8 * sW) = BitVec.ofNat 64 (k / 8) := by
    rw [ho₂.word (by unfold sW sArr; omega_arith) (by unfold sW; omega_arith), hm₁, word_writeW_self]
  obtain hR₂ : word t₂.mem B (8 * kRand) = rp := by
    rw [ho₂.word (by unfold kRand sFn sArr; omega_arith) (by unfold kRand sFn; omega_arith), hm₁,
      (writeW_outside s.mem B _ (by unfold sW; omega_arith)).word (by unfold sW kRand sFn; omega_arith) (by unfold kRand sFn; omega_arith), hR]
  obtain hs₂ := hs.congr (k₂.2.2.trans k₁.2.2)
  obtain hdi₂ : t₂.gpr .rdi = B := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hdi)
  refine WP.mono (WP.keep [.rsi, .rbx] (Q := fun t => t.gpr .rsi = rp ∧ t.gpr .rbx = off B (slot (k / 8) aN) ∧
      t.mem = t₂.mem) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, hs₂.ld (d := 8 * kRand) (by unfold kRand sFn; omega_arith),
      hs₂.ld (d := 8 * sArr aN) (by unfold sArr aN; omega_arith), hR₂, hb₂ aN (by decide)]) rfl) fun t ⟨⟨hsi, hbx, hm⟩, k₃⟩ => ?_
  refine ⟨hsi, by rw [k₃.gpr (by decide), k₂.gpr (by decide)]; exact hcx, hbx, by rw [hm]; exact hW₂,
    fun j hj => by rw [hm]; exact hb₂ j hj, ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  intro x hx
  rw [hm, ho₂ x (hx (8 * sArr 0, 64) (by simp)), hm₁, writeW_outside s.mem B _ (by unfold sW; omega_arith) x (hx (8 * sW, 8) (by simp))]

/-- The candidate's bits, and `used := out_len`. -/
theorem loadCBits_ok {s : State} {B : Addr} {Z w k : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hW : word s.mem B (8 * sW) = BitVec.ofNat 64 w)
    (hA : word s.mem B (8 * sArr aN) = off B (slot w aN)) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 k) :
    WP isa (.block [.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aN))),
      .movImm64 .rdx (BitVec.ofNat 64 (3 * 2 ^ 62)), .alu .or .rdx (.mem (ix .rbx .r12 (-8))),
      .store (ix .rbx .r12 (-8)) .rdx, .mov .rdx (.mem (at0 .rbx)), .alu .or .rdx (.imm 1), .store (at0 .rbx) .rdx,
      .mov .rax (.mem (hdr kLen)), .store (hdr kUsed) .rax]) s fun t =>
      wv t.mem B (slot w aN) w = Spec.RsaKeyGen.candidate (64 * w) (wv s.mem B (slot w aN) w) ∧
      word t.mem B (8 * kUsed) = BitVec.ofNat 64 k ∧
      Frm B [(slot w aN, 8 * (w + 2)), (8 * kUsed, 8)] s.mem t.mem ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧
      Keep [.rax, .rdx, .rbx, .r12] s t := by
  have hn := hs.nowrap
  obtain sN := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  obtain hU : 8 * kUsed + 8 ≤ slot w aN := hdr_lt_slot w aN (by decide)
  obtain hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  generalize ht : word s.mem B (slot w aN + 8 * (w - 1)) = top
  generalize hb : word s.mem B (slot w aN) = bot
  obtain hb₁ : word (s.mem.writeW (off B (slot w aN + 8 * (w - 1))) (BitVec.ofNat 64 (3 * 2 ^ 62) ||| top)) B
      (slot w aN) = bot := by
    rw [← hb]; exact (writeW_outside _ _ _ (by omega_arith)).word (by omega_arith) (by omega_arith)
  obtain hK₂ : ((s.mem.writeW (off B (slot w aN + 8 * (w - 1))) (BitVec.ofNat 64 (3 * 2 ^ 62) ||| top)).writeW
      (off B (slot w aN)) (bot ||| 1)).readW (off B (8 * kLen)) 64 = BitVec.ofNat 64 k := by
    obtain hk8 := hdr_lt_slot w aN (show kLen < 32 by decide)
    rw [← hK]
    exact ((writeW_outside _ _ _ (by omega_arith)).word (by omega_arith) (by omega_arith)).trans
      ((writeW_outside _ _ _ (by omega_arith)).word (by omega_arith) (by omega_arith))
  refine WP.mono (WP.keep [.rax, .rdx, .rbx, .r12] (Q := fun t => t.mem =
      ((s.mem.writeW (off B (slot w aN + 8 * (w - 1))) (BitVec.ofNat 64 (3 * 2 ^ 62) ||| top)).writeW
        (off B (slot w aN)) (bot ||| 1)).writeW (off B (8 * kUsed)) (BitVec.ofNat 64 k) ∧
      t.gpr .r12 = BitVec.ofNat 64 w) (by
    obtain e1 := addrm8 (b := off B (slot w aN)) (i := BitVec.ofNat 64 w) rfl rfl (show 1 ≤ w by omega_arith)
    obtain e2 : off B (slot w aN) + BitVec.ofInt 64 0 = off B (slot w aN) := by
      rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
    xrun [State.ea, hdr, hdi, hdrOff, hl sW (by decide), hl (sArr aN) (by decide), hW, hA, ix, at0, e1, e2,
      hs.ld (d := slot w aN + 8 * (w - 1)) (by omega_arith), hs.st (d := slot w aN + 8 * (w - 1)) (by omega_arith),
      hs.ld (d := slot w aN) (by omega_arith), hs.st (d := slot w aN) (by omega_arith), ht, hb₁, sx1,
      hl kLen (by decide), hK₂, hs.st (d := 8 * kUsed) (by have := hdr_lt_slot w 8 (show kUsed < 32 by decide); omega_arith)])
    rfl) fun t ⟨⟨hm, h12⟩, k⟩ => ⟨?_, ?_, ?_, h12, k⟩
  · rw [hm, (writeW_outside _ _ _ (by omega_arith)).wv (Or.inr hU) (by omega_arith)]
    refine wv_candidate hw ?_ ?_ ?_
    · rw [word_writeW_self, hb]
    · rw [(writeW_outside _ _ _ (by omega_arith)).word (by omega_arith) (by omega_arith), word_writeW_self, ht, BitVec.or_comm]
    · intro j h0 hj
      rw [(writeW_outside _ _ _ (by omega_arith)).word (by omega_arith) (by omega_arith),
        (writeW_outside _ _ _ (by omega_arith)).word (by omega_arith) (by omega_arith)]
  · rw [hm]; exact word_writeW_self _ _ _ _
  · intro x hx
    rw [hm, writeW_outside _ B _ (by omega_arith) x (hx (8 * kUsed, 8) (by simp)),
      writeW_outside _ B _ (by omega_arith) x (by have := hx (slot w aN, 8 * (w + 2)) (by simp); omega_arith),
      writeW_outside _ B _ (by omega_arith) x (by have := hx (slot w aN, 8 * (w + 2)) (by simp); omega_arith)]

/-- `loadC` but its last block: `w`, the bases, and the octets of `c`. -/
theorem loadCFront_ok {s : State} {B : Addr} {Z k : Nat} {rp : Addr} {bs : List Byte} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hZ : slot (k / 8) 8 ≤ Z) (hk1 : 16 ≤ k) (hk : k < 2 ^ 31) (hk8 : k % 8 = 0)
    (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 k) (hR : word s.mem B (8 * kRand) = rp)
    (hsrc : Src s B Z rp bs) (hbl : bs.length = k) :
    WP isa (.seq (.block (([.mov .rcx (.mem (hdr kLen)), .mov .r12 (.reg .rcx), .shift .shr .r12 3, .store (hdr sW) .r12] : List Instr) ++
      setBases ++ ([.mov .rsi (.mem (hdr kRand)), .mov .rbx (.mem (hdr (sArr aN)))] : List Instr))) loadBE) s fun t =>
      wv t.mem B (slot (k / 8) aN) (k / 8) = Spec.Rsa.os2ip bs ∧ Scr t B Z ∧ t.gpr .rdi = B ∧
      word t.mem B (8 * sW) = BitVec.ofNat 64 (k / 8) ∧ (∀ j < 8, word t.mem B (8 * sArr j) = off B (slot (k / 8) j)) ∧
      (∀ i, 16 ≤ i → i < 32 → word t.mem B (8 * i) = word s.mem B (8 * i)) ∧
      Frm B (loadCRanges (k / 8)) s.mem t.mem ∧ Keep [.rax, .rcx, .rdx, .rbx, .rsi, .rbp, .r12, .r14] s t := by
  have hn := hs.nowrap
  obtain hw8 : (k + 7) / 8 = k / 8 := by omega_arith
  obtain sN := Nat.le_trans (slot_le (w := k / 8) (show aN < 8 by decide)) hZ
  obtain hsl : ∀ r ∈ loadCRanges (k / 8), r.1 + r.2 ≤ Z := by
    have := hdr_lt_slot (k / 8) aN (show kUsed < 32 by decide)
    have := hdr_lt_slot (k / 8) aN (show sW < 32 by decide)
    simp only [loadCRanges, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl) <;> simp only [sArr, sW, kUsed, sFn] at * <;> omega_arith
  refine WP.seq (WP.mono (loadCHead_ok hs hdi hZ hk hK hR) fun t₁ ⟨hsi, hcx, hbx, hW₁, hb₁, hf₁, k₁⟩ => ?_)
  obtain hs₁ := hs.congr k₁.2.2
  obtain hf₁' : Frm B (loadCRanges (k / 8)) s.mem t₁.mem := hf₁.mono (by simp [loadCRanges])
  refine WP.mono (loadArr_ok (j := aN) hs₁ (by decide) (by rw [hw8]; exact hZ) (hsrc.congrK (InScr.of_frm hf₁' hsl) k₁)
    hbl (by omega_arith) hk hsi hcx (by rw [hw8]; exact hbx)) fun t₂ ⟨hv₂, ha₂, k₂⟩ => ?_
  rw [hw8] at hv₂ ha₂
  obtain hf₂ : Frm B (loadCRanges (k / 8)) s.mem t₂.mem :=
    hf₁'.trans (Frm.of_arrays ha₂ (fun _ hj => (List.mem_singleton.mp hj) ▸ by simp [loadCRanges]))
  refine ⟨hv₂, hs₁.congr k₂.2.2, (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hdi),
    by rw [ha₂.hslot (by decide)]; exact hW₁, fun j hj => by rw [ha₂.hslot (by unfold sArr; omega_arith)]; exact hb₁ j hj,
    fun i h1 h2 => ?_, hf₂, (k₁.trans k₂).mono (by decide)⟩
  by_cases h3 : i = kUsed
  · subst h3; rw [ha₂.hslot (by decide)]
    exact hf₁.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [sW, sArr, kUsed, sFn] <;> omega_arith) (by omega_arith)
  refine hf₂.word_eq (fun r hr => ?_) (by omega_arith)
  have := hdr_lt_slot (k / 8) aN (i := i) (by omega_arith)
  simp only [loadCRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> simp only [sW, sArr, kUsed, sFn] at * <;> omega_arith

/-- `loadC`: `c` from the first `k` octets of `rand`. -/
theorem loadC_ok {s : State} {B : Addr} {Z k : Nat} {rp : Addr} {bs : List Byte} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hZ : slot (k / 8) 8 ≤ Z) (hk1 : 16 ≤ k) (hk : k < 2 ^ 31) (hk8 : k % 8 = 0)
    (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 k) (hR : word s.mem B (8 * kRand) = rp)
    (hsrc : Src s B Z rp bs) (hbl : bs.length = k) :
    WP isa (seqs loadC) s fun t =>
      wv t.mem B (slot (k / 8) aN) (k / 8) = Spec.RsaKeyGen.candidate (8 * k) (Spec.Rsa.os2ip bs) ∧
      word t.mem B (8 * kUsed) = BitVec.ofNat 64 k ∧ word t.mem B (8 * sW) = BitVec.ofNat 64 (k / 8) ∧
      (∀ j < 8, word t.mem B (8 * sArr j) = off B (slot (k / 8) j)) ∧
      Frm B (loadCRanges (k / 8)) s.mem t.mem ∧ t.gpr .rdi = B ∧ t.gpr .r12 = BitVec.ofNat 64 (k / 8) ∧
      Keep [.rax, .rcx, .rdx, .rbx, .rsi, .rbp, .r12, .r14] s t := by
  have hn := hs.nowrap
  obtain sN := Nat.le_trans (slot_le (w := k / 8) (show aN < 8 by decide)) hZ
  unfold loadC
  simp only [seqs]
  refine WP.assoc (WP.seq (WP.mono (loadCFront_ok hs hdi hZ hk1 hk hk8 hK hR hsrc hbl)
    fun t₂ ⟨hv₂, hs₂, hdi₂, hW₂, hb₂, hhd, hf₂, k₂⟩ => ?_))
  refine WP.mono (loadCBits_ok (k := k) hs₂ hdi₂ hZ (by omega_arith) (by omega_arith) hW₂ (hb₂ aN (by decide))
    (by rw [hhd kLen (by decide) (by decide)]; exact hK)) fun t ⟨hc, hU, hf, h12, k₃⟩ => ?_
  obtain hw64 : 64 * (k / 8) = 8 * k := by omega_arith
  refine ⟨by rw [hc, hv₂, hw64], hU, ?_, fun j hj => ?_, hf₂.trans (hf.mono (by simp [loadCRanges])),
    (k₃.gpr (by decide)).trans hdi₂, h12, (k₂.trans k₃).mono (by decide)⟩
  · have h1 := hdr_lt_slot (k / 8) aN (show sW < 32 by decide)
    rw [hf.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Or.inl h1
      · exact Or.inl (by unfold sW kUsed sFn; omega_arith)) (by omega_arith)]; exact hW₂
  · have h1 := hdr_lt_slot (k / 8) aN (show sArr j < 32 by unfold sArr; omega_arith)
    rw [hf.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Or.inl h1
      · exact Or.inl (by unfold sArr kUsed sFn; omega_arith)) (by omega_arith)]; exact hb₂ j hj

end VG.Proof.RsaKeyGen.X86_64

end

end


/-!
# A candidate on x86-64: once `rand` has its octets

`MainCtx`: what `kMainWith` needs from the header and the buffers, and
what its stages keep.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- What `kMainWith` needs, for the `k` octets of a prime. -/
structure MainCtx (s : State) (B : Addr) (Z k : Nat) (op up eP pP rP : Addr) (eB pB r : List Byte) : Prop where
  scr : Scr s B Z
  rdi : s.gpr .rdi = B
  z : slot (k / 8) aTab + 2048 ≤ Z
  zx : slot (k / 8) aRm1 + 8 * (k / 8 + 2) ≤ Z
  k1 : 32 ≤ k
  k2 : k ≤ 512
  k8 : k % 8 = 0
  out : word s.mem B (8 * kOut) = op
  len : word s.mem B (8 * kLen) = BitVec.ofNat 64 k
  usedP : word s.mem B (8 * kUsedP) = up
  e : word s.mem B (8 * kE) = eP
  elen : word s.mem B (8 * kElen) = BitVec.ofNat 64 eB.length
  p : word s.mem B (8 * kP) = pP
  plen : word s.mem B (8 * kPlen) = BitVec.ofNat 64 pB.length
  rand : word s.mem B (8 * kRand) = rP
  rlen : word s.mem B (8 * kRandLen) = BitVec.ofNat 64 r.length
  esrc : Src s B Z eP eB
  psrc : Src s B Z pP pB
  rsrc : Src s B Z rP r
  el1 : 1 ≤ eB.length
  el8 : eB.length ≤ 8
  pl : pB.length = 0 ∨ pB.length = k
  rl : r.length < 2 ^ 64
  rk : k ≤ r.length
  ou : OutUp s B Z op up k

theorem seg_zero (r : List Byte) (n : Nat) : VG.Proof.RsaKeyGen.seg r 0 n = r.take n := by
  simp [VG.Proof.RsaKeyGen.seg]

/-- A stage past `loadC` keeps the first 26 header words and memory past
the scratch space. -/
theorem stage {B : Addr} {Z : Nat} {m₀ m m' : Mem} {rs : List (Nat × Nat)} (hf : Frm B rs m m')
    (h208 : ∀ r ∈ rs, 208 ≤ r.1) (hrZ : ∀ r ∈ rs, r.1 + r.2 ≤ Z)
    (h : (∀ i ≤ 25, word m B (8 * i) = word m₀ B (8 * i)) ∧ InScr B Z m₀ m) :
    (∀ i ≤ 25, word m' B (8 * i) = word m₀ B (8 * i)) ∧ InScr B Z m₀ m' :=
  ⟨fun i hi => (hf.word_eq (fun r hr => Or.inl (by have := h208 r hr; omega_arith)) (by omega_arith)).trans (h.1 i hi),
    h.2.trans (InScr.of_frm hf hrZ)⟩

/-- `finUsed st` ends a candidate. -/
theorem finUsed_end {s sX : State} {B : Addr} {Z : Nat} {op up : Addr} {k st u : Nat} (hs : Scr sX B Z)
    (hdi : sX.gpr .rdi = B) (h8 : 8 * 32 ≤ Z) (hst : st < 2 ^ 31) (hu : word sX.mem B (8 * kUsed) = BitVec.ofNat 64 u)
    (hU : word sX.mem B (8 * kUsedP) = up) (ho : OutUp sX B Z op up k)
    (hlo : ∀ i < 6, word sX.mem B (8 * i) = word s.mem B (8 * i)) (hhi : InScr B Z s.mem sX.mem)
    (kk : Keep mmRegs s sX) :
    WP isa (finUsed st) sX fun t => KEnd s t B Z op up k st u none :=
  WP.mono (finUsed_ok hs hdi h8 hst hu hU ho.upw ho.upZ) fun _ h =>
    (KEnd.of_fin ho h).trans_pre hlo (fun x hx => hhi x hx) kk ho.outZ

/-- What `kMainWith`'s frames need of the ranges `closeCheck` changes. -/
theorem closeRanges_fr (w : Nat) : (∀ r ∈ closeRanges w, 208 ≤ r.1) ∧ (∀ r ∈ closeRanges w, r.1 + r.2 ≤ slot w 8) ∧
    (∀ r ∈ closeRanges w, slot w aN + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aN) ∧
    (∀ r ∈ closeRanges w, r.1 + r.2 ≤ slot w aTab + 2048) := by
  obtain hs : VG.Proof.RsaKeyGen.SlotShape w (closeRanges w) [] [aX, aAcc, aTmp] := fun r hr => by
    simp only [closeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [.inr ⟨_, .head _, rfl⟩, .inr ⟨_, .tail _ (.head _), rfl⟩, .inr ⟨_, .tail _ (.tail _ (.head _)), rfl⟩]
  exact ⟨hs.geD rfl rfl, hs.leD rfl rfl, hs.apartW rfl rfl,
    fun r hr => Nat.le_trans (hs.leD (a := aTab) rfl rfl r hr) (Nat.le_add_right _ _)⟩

/-- The same for the ranges the trial division changes. -/
theorem trialRanges_fr (w : Nat) :
    (∀ r ∈ [(slot w aTab, 2048), (8 * kT0, 8), (8 * kT1, 8), (8 * kT2, 8)], 208 ≤ r.1) ∧
    (∀ r ∈ [(slot w aTab, 2048), (8 * kT0, 8), (8 * kT1, 8), (8 * kT2, 8)], r.1 + r.2 ≤ slot w aTab + 2048) ∧
    (∀ r ∈ [(slot w aTab, 2048), (8 * kT0, 8), (8 * kT1, 8), (8 * kT2, 8)],
      slot w aN + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aN) :=
  ⟨by rng_le, by rng_le, by rng_disj⟩

/-- The same for the ranges the gcd check changes. -/
theorem gcdRanges_fr (w : Nat) :
    (∀ r ∈ [(slot w aX, 8 * (w + 2)), (8 * kG, 8)], 208 ≤ r.1) ∧
    (∀ r ∈ [(slot w aX, 8 * (w + 2)), (8 * kG, 8)], r.1 + r.2 ≤ slot w 8) ∧
    (∀ r ∈ [(slot w aX, 8 * (w + 2)), (8 * kG, 8)], slot w aN + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aN) ∧
    (∀ r ∈ [(slot w aX, 8 * (w + 2)), (8 * kG, 8)], r.1 + r.2 ≤ slot w aTab + 2048) := by
  obtain hs : VG.Proof.RsaKeyGen.SlotShape w [(slot w aX, 8 * (w + 2)), (8 * kG, 8)] [(8 * kG, 8)] [aX] :=
    fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [.inr ⟨_, .head _, rfl⟩, .inl (.head _)]
  exact ⟨hs.geD rfl rfl, hs.leD rfl rfl, hs.apartW rfl rfl,
    fun r hr => Nat.le_trans (hs.leD (a := aTab) rfl rfl r hr) (Nat.le_add_right _ _)⟩

/-- The header words `kMainWith` keeps across `loadC`. -/
theorem loadCRanges_hdr (w : Nat) : ∀ i ∈ [kOut, kLen, kUsedP, kE, kElen, kP, kPlen, kRand, kRandLen],
    ∀ r ∈ loadCRanges w, 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i := by
  obtain h : ∀ i ∈ [kOut, kLen, kUsedP, kE, kElen, kP, kPlen, kRand, kRandLen], 8 * i + 8 ≤ VG.Impl.Bignum.hdrBytes ∧
      ∀ h ∈ ([(48, 8), (64, 64), (200, 8)] : List (Nat × Nat)), 8 * i + 8 ≤ h.1 ∨ h.1 + h.2 ≤ 8 * i := by
    decide
  exact fun i hi => VG.Proof.RsaKeyGen.hdr_of_shape (loadCRanges_shape w) (h i hi).1 (h i hi).2

end VG.Proof.RsaKeyGen.X86_64

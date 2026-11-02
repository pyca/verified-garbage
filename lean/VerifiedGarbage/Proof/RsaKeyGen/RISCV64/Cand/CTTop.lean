module

public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.Verified
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.CTMr
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
meta import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.Verified
meta import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.CTMr
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.Syms
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
meta import VerifiedGarbage.Proof.Framework.RISCV64.MRun
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# A candidate on RISC-V: the candidate and the whole function in constant time

As on PPC64LE (`Proof/RsaKeyGen/PPC64LE/Cand/{CTMain,CTTop}.lean`): two runs
from calls with the same public data (`KR`: `pubOf`, and the stack pointer)
are related by `Two` (`Proof/Bignum/RISCV64/PreCT.lean`) at each step, both
satisfying the same predicate of their call (`SG`), which fixes the registers
the next piece's addresses and branches read; the pieces by the taint
analysis, what each run satisfies after each by correctness.

On RISC-V the arguments live in the frame (`ldf`), which the taint analysis
treats as secret, so the code is cut after each load from the frame whose
value an address, a count or a branch reads (`cutW`): `out` and its length,
the working space's length, `rand`, `p`'s length and `p`, `e` and its length.
Each cut's values come from `Fr`'s words of the arguments, which `KR` makes
equal. The branches: `rand`'s length (`KRel.oL_eq`, `KRel.rL_eq`), whether
the candidate is too close to `p` (`close_agree`), `e`'s parity and whether
`e = 1` (`e` is public, `KRel.e`), and whether `gcd(c − 1, e) = 1`
(`gcd_agree`). The test (trial division, Miller–Rabin and the result) is
taken as `test_ct`'s statement (`TSt`), proven apart.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Cand

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot)
open VG.Proof.Mont (off word)
open VG.Proof.MillerRabin.RISCV64 (Env RoundImpl)
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post two_taint)
open VG.Impl.RsaKeyGen.RISCV64.Candidate (code body entry zeroOut finNone finish main restore setup loadC
  closeCheck closeCalc loadP gcdCheck loadE gcdE test ldf stf oOut oOutLen oUsed oE oELen oP oPLen oRand
  oRandLen oRead oWsLen seqs)

/-! ## The public data and the stages -/

/-- A call the contract allows, with the public data `a`. -/
def KR (a : KD) (s0 : State) : Prop := KRel a.1 s0 ∧ s0.sp = a.2

/-- A stage `X` of the call, for the public data `a`. -/
def SG (X : State → State → Prop) (a : KD) (s : State) : Prop := ∃ s0, KR a s0 ∧ X s0 s

/-- The state the test starts in: `gcd(c − 1, e) = 1` (`test_ct`). -/
def TSt (a : KD) (s : State) : Prop := ∃ s0, KR a s0 ∧ M4 s0 s ∧ Nat.gcd (candOf s0 - 1) (eV s0) = 1

theorem KR.reg {a : KD} {x y : State} (hx : KR a x) (hy : KR a y) {r : Reg} (hr : r ∈ argRegs) :
    x.gpr r = y.gpr r := hx.1.reg hy.1 hr

theorem KR.arg {a : KD} {x y : State} (hx : KR a x) (hy : KR a y) {i : Nat} (hi : i < 3) :
    stackArg x i = stackArg y i := hx.1.arg hy.1 hi

theorem KR.cw {a : KD} {x y : State} (hx : KR a x) (hy : KR a y) : cw x = cw y := by
  show oL x / 8 = oL y / 8
  rw [hx.1.oL_eq hy.1]

theorem KR.fb {a : KD} {x y : State} (hx : KR a x) (hy : KR a y) : fb x = fb y := by
  show x.sp - _ = y.sp - _
  rw [hx.2, hy.2]

theorem KR.eV {a : KD} {x y : State} (hx : KR a x) (hy : KR a y) : eV x = eV y := by
  rw [eV_eq, eV_eq, hx.1.e hy.1]

/-- A stage fixes the registers `rs`: their values are a function `f` of the
call that the public data fixes. -/
theorem pins_of {X : State → State → Prop} {rs : List Reg} (f : State → Reg → BitVec 64)
    (hf : ∀ a x y, KR a x → KR a y → ∀ r ∈ rs, f x r = f y r)
    (hx : ∀ s0 t, X s0 t → ∀ r ∈ rs, t.gpr r = f s0 r) : Pins (SG X) rs := by
  rintro a s₁ s₂ ⟨x, kx, hx₁⟩ ⟨y, ky, hy₂⟩ r hr
  rw [hx _ _ hx₁ r hr, hx _ _ hy₂ r hr]
  exact hf a x y kx ky r hr

/-- Nothing pinned. -/
theorem pins_nil {α : Type} {X : α → State → Prop} : Pins X [] := fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil

/-- A weaker stage. -/
theorem wk {X X' : State → State → Prop} {c : Prog isa} {Q : State → State → Prop}
    (hX : ∀ a s0 t, KR a s0 → X s0 t → X' s0 t) (h : RelCT isa (Two (SG X')) c Q) : RelCT isa (Two (SG X)) c Q :=
  h.mono (fun _ _ ⟨a, ⟨s0, k, x⟩, ⟨s0', k', x'⟩, hsp⟩ => ⟨a, ⟨s0, k, hX _ _ _ k x⟩, ⟨s0', k', hX _ _ _ k' x'⟩, hsp⟩)
    fun _ _ h => h

/-- A cut after `c₁`: what `c₁` leaves (`Y`), and that the rest still runs
to `X'`. -/
theorem cutW {X Y X' : State → State → Prop} {c₁ c₂ : Prog isa} {Q : State → State → Prop}
    (hy : ∀ s0 s, X s0 s → WP isa c₁ s (Y s0)) (h : ∀ s0 s, X s0 s → WP isa (.seq c₁ c₂) s (X' s0))
    (t₁ : RelCT isa (Two (SG X)) c₁ fun _ _ => True)
    (t₂ : RelCT isa (Two (SG fun s0 t => Y s0 t ∧ WP isa c₂ t (X' s0))) c₂ Q) :
    RelCT isa (Two (SG X)) (.seq c₁ c₂) Q :=
  RelCT.seq (two_post t₁ fun _ s ⟨s0, k, hx⟩ => WP.mono (WP.and (hy s0 s hx) (WP.seq_iff.mp (h s0 s hx)))
    fun _ ⟨y, w⟩ => ⟨s0, k, y, w⟩) t₂

/-- The stage the rest of a piece runs to. -/
theorem toPost {Y X' : State → State → Prop} {c : Prog isa}
    (t : RelCT isa (Two (SG fun s0 t => Y s0 t ∧ WP isa c t (X' s0))) c fun _ _ => True) :
    RelCT isa (Two (SG fun s0 t => Y s0 t ∧ WP isa c t (X' s0))) c (Two (SG X')) :=
  two_post t fun _ _ ⟨s0, k, _, w⟩ => WP.mono w fun _ ht => ⟨s0, k, ht⟩

/-- A branch whose condition the stage fixes. -/
theorem iteW {Y : State → State → Prop} {cond : isa.Cond} {th el : Prog isa} {Q : State → State → Prop}
    (hc : ∀ a s₁ s₂, SG Y a s₁ → SG Y a s₂ → isa.eval cond s₁ = isa.eval cond s₂)
    (ht : RelCT isa (Two (SG fun s0 t => Y s0 t ∧ isa.eval cond t = some true)) th Q)
    (he : RelCT isa (Two (SG fun s0 t => Y s0 t ∧ isa.eval cond t = some false)) el Q) :
    RelCT isa (Two (SG Y)) (.ite cond th el) Q := by
  refine RelCT.ite (fun s₁ s₂ ⟨a, h₁, h₂, _⟩ => hc a _ _ h₁ h₂) (ht.mono ?_ fun _ _ h => h)
    (he.mono ?_ fun _ _ h => h)
  · rintro s₁ s₂ ⟨⟨a, ⟨x, kx, y₁⟩, ⟨x', kx', y₂⟩, hsp⟩, hb⟩
    exact ⟨a, ⟨x, kx, y₁, hb⟩, ⟨x', kx', y₂, (hc a _ _ ⟨x, kx, y₁⟩ ⟨x', kx', y₂⟩).symm.trans hb⟩, hsp⟩
  · rintro s₁ s₂ ⟨⟨a, ⟨x, kx, y₁⟩, ⟨x', kx', y₂⟩, hsp⟩, hb⟩
    exact ⟨a, ⟨x, kx, y₁, hb⟩, ⟨x', kx', y₂, (hc a _ _ ⟨x, kx, y₁⟩ ⟨x', kx', y₂⟩).symm.trans hb⟩, hsp⟩

/-- A branch, with what the rest runs to. -/
theorem iteK {Y X' : State → State → Prop} {cond : isa.Cond} {th el : Prog isa} {Q : State → State → Prop}
    (hc : ∀ a s₁ s₂, SG Y a s₁ → SG Y a s₂ → isa.eval cond s₁ = isa.eval cond s₂)
    (ht : RelCT isa (Two (SG fun s0 t => (Y s0 t ∧ isa.eval cond t = some true) ∧ WP isa th t (X' s0))) th Q)
    (he : RelCT isa (Two (SG fun s0 t => (Y s0 t ∧ isa.eval cond t = some false) ∧ WP isa el t (X' s0))) el Q) :
    RelCT isa (Two (SG fun s0 t => Y s0 t ∧ WP isa (.ite cond th el) t (X' s0))) (.ite cond th el) Q :=
  iteW (fun a s₁ s₂ ⟨x, kx, y₁, _⟩ ⟨x', kx', y₂, _⟩ => hc a s₁ s₂ ⟨x, kx, y₁⟩ ⟨x', kx', y₂⟩)
    (wk (fun _ _ _ _ ⟨⟨y, w⟩, hb⟩ => ⟨⟨y, hb⟩, WP.ite_true w hb⟩) ht)
    (wk (fun _ _ _ _ ⟨⟨y, w⟩, hb⟩ => ⟨⟨y, hb⟩, WP.ite_false w hb⟩) he)

/-- `a; (b; c)` as `(a; b); c`. -/
theorem relCT_assocR {P Q : State → State → Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq a (.seq b c)) Q) : RelCT isa P (.seq (.seq a b) c) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq e₁ c₁ =>
    cases e₁ with
    | seq a₁ b₁ =>
      cases e₂ with
      | seq e₂ c₂ =>
        cases e₂ with
        | seq a₂ b₂ =>
          obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ c₁)) (.seq a₂ (.seq b₂ c₂))
          simp only [List.append_assoc] at ht ⊢
          exact ⟨ht, hq⟩

/-- A block that starts a sequence, split in two. -/
theorem relCT_seq_block {P Q : State → State → Prop} {l₁ l₂ : List Instr} {c : Prog isa}
    (h : RelCT isa P (.seq (.block l₁) (.seq (.block l₂) c)) Q) : RelCT isa P (.seq (.block (l₁ ++ l₂)) c) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq a₁ c₁ =>
    cases e₂ with
    | seq a₂ c₂ =>
      rw [Exec.block_iff, execBlock_append] at a₁ a₂
      obtain ⟨⟨x₁, u₁⟩, hx₁, hb₁⟩ := Option.bind_eq_some_iff.mp a₁
      obtain ⟨⟨y₁, v₁⟩, hy₁, he₁⟩ := Option.map_eq_some_iff.mp hb₁
      obtain ⟨⟨x₂, u₂⟩, hx₂, hb₂⟩ := Option.bind_eq_some_iff.mp a₂
      obtain ⟨⟨y₂, v₂⟩, hy₂, he₂⟩ := Option.map_eq_some_iff.mp hb₂
      simp only [Prod.mk.injEq] at he₁ he₂
      obtain ⟨rfl, rfl⟩ := he₁
      obtain ⟨rfl, rfl⟩ := he₂
      obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.block hx₁) (.seq (.block hy₁) c₁))
        (.seq (.block hx₂) (.seq (.block hy₂) c₂))
      simp only [List.append_assoc] at ht ⊢
      exact ⟨ht, hq⟩

theorem wp_seq_block {l₁ l₂ : List Instr} {c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.block (l₁ ++ l₂)) c) s Q) : WP isa (.seq (.block l₁) (.seq (.block l₂) c)) s Q := by
  rw [WP.seq_iff, WP.block_append_iff] at h
  exact WP.seq (WP.mono h fun _ h => WP.seq h)

/-- Allocating and freeing a frame leaks nothing. -/
theorem relCT_alloc {bytes : Nat} {bd : Prog isa} {P R : State → State → Prop}
    (hb : RelCT isa (fun a b => ∃ s t, P s t ∧ a = allocd bytes s ∧ b = allocd bytes t) bd R) :
    RelCT isa P (.frame (.alloc bytes) bd (.free bytes)) fun _ _ => True := by
  intro s t ts tt s' t' hp es et
  have alloc_eq : ∀ {a b : State}, isa.push (.alloc bytes) a = some b → b = allocd bytes a := by
    intro a b h
    simp only [isa, push] at h
    split at h <;> cases h
    rfl
  cases es with
  | frame ps bs qs =>
    cases et with
    | frame pt bt qt =>
      have ea := alloc_eq ps
      have eb := alloc_eq pt
      subst ea eb
      obtain ⟨rfl, _⟩ := hb _ _ _ _ _ _ ⟨s, t, hp, rfl, rfl⟩ bs bt
      exact ⟨rfl, trivial⟩

/-! ## Loads from the frame -/

section
variable {s0 : State}

theorem Fr.write {s : State} (h : Fr s0 s) {r : Reg} (hr : r ≠ .s11) (v : BitVec 64) : Fr s0 (s.write r v) :=
  h.step (sp_write _ _ _) (rd_write _ _ _) (wr_write _ _ _) (gpr_write_of_ne _ _ (Ne.symm hr))
    (by rw [mem_write]; exact Frame.refl _ _)

theorem ldf_wp {s : State} (h : Fr s0 s) {r : Reg} {o : Nat} (ho : o + 8 ≤ 192) (h8 : o % 8 = 0)
    {rest : List Instr} {Q : State → Prop} (k : WP isa (.block rest) (s.write r (s.mem.readW (fw s0 o) 64)) Q) :
    WP isa (.block (ldf r o :: rest)) s Q :=
  WP.block_cons_iff.mpr ⟨_, h.load ho h8, k⟩

/-- The frame's `s11` is public. -/
def fbOf (s0 : State) (_ : Reg) : BitVec 64 := fb s0

theorem fbOf_agree : ∀ (a : KD) (x y : State), KR a x → KR a y → ∀ r ∈ ([.s11] : List Reg), fbOf x r = fbOf y r :=
  fun _ _ _ kx ky _ _ => kx.fb ky

/-- `Fr` pins `s11`. -/
theorem pins_fr {X : State → State → Prop} (hx : ∀ s0 t, X s0 t → Fr s0 t) : Pins (SG X) [.s11] :=
  pins_of fbOf fbOf_agree fun s0 t h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (hx s0 t h).s11

end

/-! ## The ends: `finish` and `finNone` -/

/-- Two registers that the arguments' registers give. -/
def argPair (r₁ q₁ _r₂ q₂ : Reg) (s0 : State) (r : Reg) : BitVec 64 := if r = r₁ then s0.gpr q₁ else s0.gpr q₂

theorem argPair_agree {r₁ q₁ r₂ q₂ : Reg} (h₁ : q₁ ∈ argRegs) (h₂ : q₂ ∈ argRegs) (rs : List Reg) :
    ∀ (a : KD) (x y : State), KR a x → KR a y → ∀ r ∈ rs, argPair r₁ q₁ r₂ q₂ x r = argPair r₁ q₁ r₂ q₂ y r :=
  fun _ _ _ kx ky r _ => by
    unfold argPair
    split
    · exact kx.reg ky h₁
    · exact kx.reg ky h₂

/-- `finish`'s loads: the octets read, and `used`. -/
theorem finA_ok {s0 s : State} (h : Fr s0 s) :
    WP isa (.block [ldf .t2 oRead, ldf .t3 oUsed]) s fun t => t.gpr .t3 = s0.gpr .a2 := by
  refine ldf_wp h (by decide) (by decide) (ldf_wp (h.write (by decide) _) (by decide) (by decide) (WP.block_nil ?_))
  rw [gpr_write_self, mem_write, h.wUsed]

theorem finish_rel (r : Nat) (hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) :
    RelCT isa (Two (SG fun s0 t => Fr s0 t)) (finish r) fun _ _ => True := by
  have hr' : r < 2048 := by omega
  have hw : ∀ s0 s, Fr s0 s → WP isa (.seq (.block [ldf .t2 oRead, ldf .t3 oUsed])
      (.block [.store .d .t2 .t3 0, .li .a0 (r : Int)])) s fun _ => True := fun s0 s h => by
    have := finish_ok r h hr'
    rw [show finish r = .block ([ldf .t2 oRead, ldf .t3 oUsed] ++ [.store .d .t2 .t3 0, .li .a0 r]) from rfl,
      WP.block_append_iff] at this
    exact WP.seq (WP.mono this fun _ h => WP.mono h fun _ _ => trivial)
  have pin : Pins (SG fun s0 t => t.gpr .t3 = s0.gpr .a2) [.t3] :=
    pins_of (argPair .t3 .a2 .t3 .a2) (argPair_agree (by decide) (by decide) _)
      fun s0 t h r hr => by simp only [List.mem_singleton] at hr; subst hr; simp only [argPair, ite_true]; exact h
  show RelCT isa _ (.block ([ldf .t2 oRead, ldf .t3 oUsed] ++ [.store .d .t2 .t3 0, .li .a0 r])) _
  rcases hr with rfl | rfl | rfl | rfl <;>
  exact RelCT.block_append (cutW (Y := fun s0 t => t.gpr .t3 = s0.gpr .a2) (X' := fun _ _ => True)
    (fun _ _ h => finA_ok h) hw (two_taint _ (pins_fr fun _ _ h => h) (by taint_decide))
    (wk (fun _ _ _ _ h => h.1) (two_taint [.t3] pin (by taint_decide))))

/-- `finNone`'s store of the octets read, 0. -/
theorem liStf_ok {s0 s : State} (h : Fr s0 s) : WP isa (.block [.li .t2 0, stf .t2 oRead]) s (Fr s0) := by
  refine WP.block_cons_iff.mpr ⟨_, exec_li (imm := 0) (by decide), WP.block_cons_iff.mpr
    ⟨_, (h.write (r := .t2) (by decide) _).store (by decide) (by decide), WP.block_nil ?_⟩⟩
  exact (h.write (r := .t2) (by decide) _).step rfl rfl rfl rfl (rdW_frame _ _)

theorem finNone_rel : RelCT isa (Two (SG fun s0 t => Fr s0 t)) finNone fun _ _ => True :=
  cutW (Y := fun s0 t => Fr s0 t) (X' := fun _ _ => True) (fun _ _ h => liStf_ok h)
    (fun _ _ h => WP.seq (WP.mono (liStf_ok h) fun _ ht => WP.mono (finish_ok 0 ht (by decide)) fun _ _ => trivial))
    (two_taint _ (pins_fr fun _ _ h => h) (by taint_decide)) (wk (fun _ _ _ _ h => h.1) (finish_rel 0 (by decide)))

/-! ## The body -/

/-- After the entry. -/
def XE (s0 t : State) : Prop := Fr s0 t ∧ t.gpr .s6 = stackArg s0 1 ∧ t.syms = s0.syms

/-- After `out`'s zeroing. -/
def XZ (s0 t : State) : Prop := Ctx s0 t ∧ t.gpr .s6 = stackArg s0 1 ∧ t.syms = s0.syms

/-- After the test of `rand`'s length. -/
def XF (s0 t : State) : Prop :=
  XZ s0 t ∧ t.gpr .t2 = BitVec.ofNat 64 (if oL s0 ≤ rL s0 then 1 else 0)

theorem zA_ok {s0 s : State} (h : Fr s0 s) :
    WP isa (.block [ldf .t3 oOut, ldf .t5 oOutLen, .li .t2 0]) s fun t =>
      t.gpr .t3 = s0.gpr .a0 ∧ t.gpr .t5 = s0.gpr .a1 := by
  refine ldf_wp h (by decide) (by decide) (ldf_wp (h.write (by decide) _) (by decide) (by decide)
    (WP.block_cons_iff.mpr ⟨_, exec_li (imm := 0) (by decide), WP.block_nil ?_⟩))
  simp only [gpr_write_self, gpr_write_of_ne _ _ (show ¬ Reg.t3 = Reg.t2 by decide),
    gpr_write_of_ne _ _ (show ¬ Reg.t3 = Reg.t5 by decide), gpr_write_of_ne _ _ (show ¬ Reg.t5 = Reg.t2 by decide),
    mem_write, h.wOut, h.wOutLen]
  exact ⟨trivial, trivial⟩

theorem pins_args {X : State → State → Prop} {r₁ q₁ r₂ q₂ : Reg} (h₁ : q₁ ∈ argRegs) (h₂ : q₂ ∈ argRegs)
    (hne : r₂ ≠ r₁) (hx : ∀ s0 t, X s0 t → t.gpr r₁ = s0.gpr q₁ ∧ t.gpr r₂ = s0.gpr q₂) : Pins (SG X) [r₁, r₂] :=
  pins_of (argPair r₁ q₁ r₂ q₂) (argPair_agree h₁ h₂ _) fun s0 t h r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [argPair, ite_true]; exact (hx s0 t h).1
    · simp only [argPair, hne, ite_false]; exact (hx s0 t h).2

theorem zero_rel : RelCT isa (Two (SG XE)) zeroOut (Two (SG XZ)) := by
  unfold zeroOut
  exact cutW (Y := fun s0 t => t.gpr .t3 = s0.gpr .a0 ∧ t.gpr .t5 = s0.gpr .a1) (X' := XZ)
    (fun _ _ h => zA_ok h.1)
    (fun _ _ ⟨hf, s6, sy⟩ => WP.mono_syms (zeroOut_ok hf) fun _ ⟨c, _, k⟩ sy' =>
      ⟨c, (k.gpr (by decide)).trans s6, sy'.trans sy⟩)
    (two_taint _ (pins_fr fun _ _ h => h.1) (by taint_decide))
    (toPost (wk (fun _ _ _ _ h => h.1)
      (two_taint _ (pins_args (by decide) (by decide) (by decide) fun _ _ h => h) (by taint_decide))))

theorem flag_rel : RelCT isa (Two (SG XZ))
    (.block ([ldf .t3 oRandLen, ldf .t4 oOutLen] ++ VG.Impl.MillerRabin.RISCV64.Search.geFlag .t2 .t3 .t4))
    (Two (SG XF)) :=
  two_post (two_taint _ (pins_fr fun _ _ h => h.1.fr) (by taint_decide)) fun _ _ ⟨s0, k, c, s6, sy⟩ =>
    WP.mono_syms (WP.rdwr (WP.keep [.t3, .t4, .t2] (flagI c.fr) (by rfl) (by rfl)))
      fun _ ⟨⟨⟨f₂, m₂⟩, k₂⟩, _, _, sp₂⟩ sy₂ => ⟨s0, k, ⟨c.keep k₂ m₂ sp₂, (k₂.gpr (by decide)).trans s6, sy₂.trans sy⟩, f₂⟩

theorem len_eval : ∀ (a : KD) (s₁ s₂ : State), SG XF a s₁ → SG XF a s₂ →
    isa.eval (.zero .t2) s₁ = isa.eval (.zero .t2) s₂ := by
  rintro a s₁ s₂ ⟨x, kx, -, hx⟩ ⟨y, ky, -, hy⟩
  rw [VG.RISCV64.Steps.eval_zero, VG.RISCV64.Steps.eval_zero, hx, hy, kx.1.oL_eq ky.1, kx.1.rL_eq ky.1]

theorem hav_of {s0 t : State} (f : t.gpr .t2 = BitVec.ofNat 64 (if oL s0 ≤ rL s0 then 1 else 0))
    (ev : isa.eval (.zero .t2) t = some false) : oL s0 ≤ rL s0 := by
  rw [VG.RISCV64.Steps.eval_zero_ofNat _ _ (by split <;> decide) f] at ev
  by_contra hc; simp only [hc, ↓reduceIte] at ev; exact absurd ev (by decide)

theorem body_rel {trial : Prog isa} (D : DivOk trial) (R : RoundImpl)
    (hmain : RelCT isa (Two (SG MIn)) (main trial R.name R.code) fun _ _ => True) :
    RelCT isa (Two (SG fun s0 u => u = allocd 192 s0)) (body trial R.name R.code) fun _ _ => True := by
  unfold body
  simp only [seqs]
  refine RelCT.seq (two_post (Ψ := SG XE) (two_taint [] pins_nil (by taint_decide)) fun _ u ⟨s0, k, hu⟩ => by
    subst hu; exact WP.mono (entry_ok k.1.1) fun _ ⟨f, s6, _, sy⟩ => ⟨s0, k, f, s6, sy⟩)
    (RelCT.seq zero_rel (RelCT.seq flag_rel (RelCT.seq (two_post (Ψ := SG fun _ _ => True)
      (iteW len_eval (wk (fun _ _ _ _ h => h.1.1.1.fr) finNone_rel)
        (wk (fun _ _ _ k ⟨⟨⟨c, s6, sy⟩, f⟩, ev⟩ => ⟨c, s6, hav_of f ev, sy, k.1.2.1⟩) hmain))
      fun _ s ⟨s0, k, ⟨c, s6, sy⟩, f⟩ => ?_) (two_taint [] pins_nil (by taint_decide)))))
  have hp := c.fr.pre
  refine WP.ite _ (VG.RISCV64.Steps.eval_zero_ofNat _ _ (by split <;> decide) f) (fun hz => ?_) (fun hz => ?_)
  · have hav : ¬ oL s0 ≤ rL s0 := by
      intro hc; simp only [hc, ↓reduceIte] at hz; exact absurd hz (by decide)
    exact WP.mono (finNone_post c (cOp_none hp hav)) fun _ _ => ⟨s0, k, trivial⟩
  · have hav : oL s0 ≤ rL s0 := by
      by_contra hc; simp only [hc, ↓reduceIte] at hz; exact absurd hz (by decide)
    exact WP.mono (main_ok D R ⟨c, s6, hav, sy, k.1.2.1⟩) fun _ _ => ⟨s0, k, trivial⟩

/-- The whole function, from the main part. -/
theorem code_rel {trial : Prog isa} (D : DivOk trial) (R : RoundImpl)
    (hmain : RelCT isa (Two (SG MIn)) (main trial R.name R.code) fun _ _ => True) :
    RelCT isa (Two KR) (code trial R.name R.code) fun _ _ => True :=
  relCT_alloc ((body_rel D R hmain).mono (fun _ _ ⟨s, t, ⟨a, h₁, h₂, hsp⟩, e₁, e₂⟩ =>
    ⟨a, ⟨s, h₁, e₁⟩, ⟨t, h₂, e₂⟩, by rw [e₁, e₂]; simp only [allocd, hsp]⟩) fun _ _ h => h)

/-- Constant time, from the main part's. -/
theorem cand_ct_of {trial : Prog isa} (D : DivOk trial) (R : RoundImpl)
    (hmain : RelCT isa (Two (SG MIn)) (main trial R.name R.code) fun _ _ => True) :
    ConstantTime isa contract.pre contract.pub (code trial R.name R.code) :=
  RelCT.constantTime ((code_rel D R hmain).mono (fun s₁ _ ⟨h₁, h₂, hp⟩ =>
    ⟨(pubOf s₁, s₁.sp), ⟨⟨(pre_facts h₁).1, (pre_facts h₁).2, rfl⟩, rfl⟩,
      ⟨⟨(pre_facts h₂).1, (pre_facts h₂).2, (pub_of hp).2.symm⟩, (pub_of hp).1.symm⟩, (pub_of hp).1⟩)
    fun _ _ h => h)

/-! ## The main part's pieces, by correctness -/

section
open VG.Impl.MillerRabin.RISCV64.Search (sth hWsLen hW hStride)
open VG.Impl.Bignum.RISCV64.PublicChecked (base)
open VG.Impl.RsaKeyGen.RISCV64.Candidate (nArr aP)
open VG.Proof.Mont (ofs Outside writeW_outside)

/-- `setup`'s header: the lengths and the stride. -/
def setupA : List Instr :=
  [ldf .t2 oWsLen, sth .t2 hWsLen, ldf .t2 oOutLen, .shift .srl .d .t0 .t2 3, sth .t0 hW,
    .addi .s5 .t0 2, .shift .sll .d .s5 .s5 3, sth .s5 hStride, .addi .a7 .s6 VG.Impl.Bignum.hdrBytes]

/-- `setup`'s arrays' addresses and the count of its zeroing. -/
def setupB : List Instr :=
  (List.range 8).flatMap (fun j => base .t2 j ++ [sth .t2 (8 + j)]) ++
    [.addi .t3 .a7 0, .li .t5 nArr, .mul .t5 .t5 .s5, .shift .srl .d .t5 .t5 3, .li .t2 0]

theorem setup_eq : setup = .seq (.block (setupA ++ setupB))
    (VG.Impl.Bignum.RISCV64.countLoop .t5 [.store .d .t2 .t3 0, .addi .t3 .t3 8]) := rfl

/-- The registers `Env` reads, from the call. -/
def EVs (s0 t : State) : Prop :=
  t.gpr .a7 = off (stackArg s0 1) (slot (cw s0) 0) ∧ t.gpr .s5 = BitVec.ofNat 64 (8 * (cw s0 + 2)) ∧
    t.gpr .t0 = BitVec.ofNat 64 (cw s0) ∧ t.gpr .s6 = stackArg s0 1

theorem EVs.of_env {s0 t : State} (h : Env t (stackArg s0 1) (8 * sL s0) (cw s0)) : EVs s0 t :=
  ⟨h.a7, h.s5, h.t0, h.s6⟩

theorem setupA_ok {s0 s : State} (h : Fr s0 s) (h6 : s.gpr .s6 = stackArg s0 1) :
    WP isa (.block setupA) s (EVs s0) := by
  have hp := h.pre
  obtain ⟨hw, -, -⟩ := cw_facts hp
  generalize hwd : cw s0 = w at hw
  rw [show EVs s0 = fun t => t.gpr .a7 = off (stackArg s0 1) (slot w 0) ∧
    t.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.gpr .t0 = BitVec.ofNat 64 w ∧ t.gpr .s6 = stackArg s0 1 by
      rw [← hwd]; rfl]
  generalize hB : stackArg s0 1 = B at h6
  generalize hSL : sL s0 = SL
  have hs : Scr s B (8 * SL) := hB ▸ hSL ▸ scr_of h
  have hnw := hs.nowrap
  have hw4 : 4 ≤ w := by have := hp.valid.1; simp only [oL] at hw; omega_arith
  have hw64 : w ≤ 64 := by have := oL_le hp; simp only [oL] at this hw; omega_arith
  have hsc : 16 * (8 * w) + 32 ≤ SL := by
    have := hp.scr; simp only [Spec.Rsa.scratchWords] at this; simp only [oL] at hw; rw [← hSL]; simp only [sL]
    omega_arith
  have al : ∀ o, o % 8 = 0 → (fb s0 + BitVec.ofNat 64 o).toNat % 8 = 0 := fun o h8 => fw_al hp h8
  have inr : ∀ o, o + 8 ≤ 192 → InRegions (s.rd ++ s.wr) (fb s0 + BitVec.ofNat 64 o) 8 := fun o ho =>
    ⟨kF s0, List.mem_append_right _ (by rw [h.wr]; exact List.mem_cons_self), kF_contains ho⟩
  have r184 : s.mem.readW (fb s0 + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 SL := by
    rw [show fb s0 + BitVec.ofNat 64 184 = fw s0 oWsLen from rfl, h.wl, ← hSL, sL, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  have r112 : s.mem.readW (fb s0 + BitVec.ofNat 64 112) 64 = BitVec.ofNat 64 (8 * w) := by
    rw [show fb s0 + BitVec.ofNat 64 112 = fw s0 oOutLen from rfl, h.wOutLen, ← hw, oL, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  have e3 : BitVec.ofNat 64 (8 * w) >>> 3 = BitVec.ofNat 64 w := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega_arith
  have e5 : (BitVec.ofNat 64 w + BitVec.ofNat 64 2) <<< 3 = BitVec.ofNat 64 (8 * (w + 2)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq]
    omega_arith
  have r112' : (s.mem.writeW (off B 0) (BitVec.ofNat 64 SL)).readW (fb s0 + 112#64) 64 =
      BitVec.ofNat 64 (8 * w) := by
    rw [← r112]
    refine ((Frame.refl [cS s0] s.mem).writeW (r := cS s0) List.mem_cons_self _ ?_).readW (r := ⟨fw s0 112, 8⟩)
      (Region.contains_self _ _) (fun ρ hρ => ?_) (by decide)
    · have hc0 := Offset.contains_base (stackArg s0 1) (d := 0) (n := 8) (k := (stackArg s0 2).toNat * 8)
        (by simp only [sL] at hSL; omega_arith) (by decide)
      rw [← hB]; exact hc0
    · simp only [List.mem_singleton] at hρ; subst hρ; exact hp.FS.sub_left (fw_sub s0 (by decide))
  unfold setupA
  brun [ldf, sth, oWsLen, oOutLen, hWsLen, hW, hStride, h.s11, r112', al 184 (by decide), al 112 (by decide),
    inr 184 (by decide), inr 112 (by decide), r184, r112, h6, e3, e5, hs.st (d := 0) (n := 8) (by omega_arith),
    hs.st (d := 48) (n := 8) (by omega_arith), hs.st (d := 224) (n := 8) (by omega_arith),
    hs.al8 (d := 0) (by omega_arith) (by decide), hs.al8 (d := 48) (by omega_arith) (by decide),
    hs.al8 (d := 224) (by omega_arith) (by decide), (show VG.Impl.Bignum.hdrBytes < 2048 by decide)]
  simp [slot, VG.Impl.Bignum.hdrBytes]

/-- `loadP`'s first block: `p`'s array, `p` and `out_len`. -/
def loadPA : List Instr := base .t2 aP ++ [.addi .a7 .t2 0, ldf .s7 oP, ldf .s8 oOutLen]

theorem loadPA_ok {s0 s : State} (hf : Fr s0 s) (h : Env s (stackArg s0 1) (8 * sL s0) (cw s0)) :
    WP isa (.block loadPA) s fun t => (t.gpr .s7 = s0.gpr .a5 ∧ t.gpr .s8 = s0.gpr .a1) ∧
      t.gpr .a7 = off (stackArg s0 1) (slot (cw s0) aP) ∧ t.gpr .s5 = BitVec.ofNat 64 (8 * (cw s0 + 2)) ∧
      t.gpr .t0 = BitVec.ofNat 64 (cw s0) ∧ t.gpr .s6 = stackArg s0 1 := by
  have hp := hf.pre
  have al : ∀ o, o % 8 = 0 → (fb s0 + BitVec.ofNat 64 o).toNat % 8 = 0 := fun o h8 => fw_al hp h8
  have inr : ∀ o, o + 8 ≤ 192 → InRegions (s.rd ++ s.wr) (fb s0 + BitVec.ofNat 64 o) 8 := fun o ho =>
    ⟨kF s0, List.mem_append_right _ (by rw [hf.wr]; exact List.mem_cons_self), kF_contains ho⟩
  have r144 : s.mem.readW (fb s0 + BitVec.ofNat 64 144) 64 = s0.gpr .a5 := hf.wP
  have r112 : s.mem.readW (fb s0 + BitVec.ofNat 64 112) 64 = s0.gpr .a1 := hf.wOutLen
  unfold loadPA
  rw [WP.block_append_iff]
  refine WP.mono (h.base (rd := .t2) (by decide) aP) fun t₁ ⟨⟨a2, m₁⟩, k₁⟩ => ?_
  have i1 : ∀ o, o + 8 ≤ 192 → InRegions (t₁.rd ++ t₁.wr) (fb s0 + BitVec.ofNat 64 o) 8 := fun o ho => by
    rw [k₁.2.1, k₁.2.2]; exact inr o ho
  have g5 : t₁.gpr .s5 = BitVec.ofNat 64 (8 * (cw s0 + 2)) := (k₁.gpr (by decide)).trans h.s5
  have g0 : t₁.gpr .t0 = BitVec.ofNat 64 (cw s0) := (k₁.gpr (by decide)).trans h.t0
  have g6 : t₁.gpr .s6 = stackArg s0 1 := (k₁.gpr (by decide)).trans h.s6
  brun [a2, ldf, oP, oOutLen, (k₁.gpr (by decide)).trans hf.s11, al 144 (by decide), al 112 (by decide),
    i1 144 (by decide), i1 112 (by decide), m₁, r144, r112, BitVec.add_zero, g5, g0, g6]

end

/-! ## The main part in constant time -/

theorem pins_by {X : State → State → Prop} {rs : List Reg}
    (hx : ∀ a s₁ s₂ x y, KR a x → KR a y → X x s₁ → X y s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    Pins (SG X) rs :=
  fun a s₁ s₂ ⟨x, kx, h₁⟩ ⟨y, ky, h₂⟩ => hx a s₁ s₂ x y kx ky h₁ h₂

theorem EVs.agree {a : KD} {x y s₁ s₂ : State} (kx : KR a x) (ky : KR a y) (hx : EVs x s₁) (hy : EVs y s₂) :
    ∀ r ∈ ([.a7, .s5, .t0, .s6] : List Reg), s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [hx.1, hy.1, kx.arg ky (by decide), kx.cw ky]
  · rw [hx.2.1, hy.2.1, kx.cw ky]
  · rw [hx.2.2.1, hy.2.2.1, kx.cw ky]
  · rw [hx.2.2.2, hy.2.2.2, kx.arg ky (by decide)]

theorem pins_ev {X : State → State → Prop} (h : ∀ s0 t, X s0 t → EVs s0 t) : Pins (SG X) [.a7, .s5, .t0, .s6] :=
  pins_by fun _ _ _ _ _ kx ky h₁ h₂ => EVs.agree kx ky (h _ _ h₁) (h _ _ h₂)

theorem EVs.write {s0 t : State} (h : EVs s0 t) {r : Reg} (hr : r ∉ ([.a7, .s5, .t0, .s6] : List Reg))
    (v : BitVec 64) : EVs s0 (t.write r v) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h7, h5, h0, h6⟩ := hr
  exact ⟨by rw [gpr_write_of_ne _ _ (Ne.symm h7)]; exact h.1, by rw [gpr_write_of_ne _ _ (Ne.symm h5)]; exact h.2.1,
    by rw [gpr_write_of_ne _ _ (Ne.symm h0)]; exact h.2.2.1, by rw [gpr_write_of_ne _ _ (Ne.symm h6)]; exact h.2.2.2⟩

theorem setup_rel : RelCT isa (Two (SG MIn)) setup (Two (SG M1)) := by
  rw [setup_eq]
  exact relCT_seq_block (cutW (Y := EVs) (X' := M1) (fun _ _ h => setupA_ok h.ctx.fr h.s6)
    (fun _ _ h => wp_seq_block (setupS h))
    (two_taint [.s11, .s6] (pins_by fun _ _ _ _ _ kx ky h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.ctx.fr.s11, h₂.ctx.fr.s11, kx.fb ky]
      · rw [h₁.s6, h₂.s6, kx.arg ky (by decide)]) (by taint_decide))
    (toPost (wk (fun _ _ _ _ h => h.1) (two_taint _ (pins_ev fun _ _ h => h) (by taint_decide)))))

/-- After `loadC`'s loads of `rand` and `out_len`. -/
def YC (s0 t : State) : Prop :=
  (t.gpr .s7 = s0.gpr .a7 ∧ t.gpr .s8 = s0.gpr .a1) ∧ EVs s0 t ∧ t.gpr .s11 = fb s0

theorem pins_YC : Pins (SG YC) [.s11, .s7, .s8, .a7, .t0, .s6, .s5] :=
  pins_by fun _ _ _ _ _ kx ky h₁ h₂ r hr => by
    have ev := EVs.agree kx ky h₁.2.1 h₂.2.1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h₁.2.2, h₂.2.2, kx.fb ky]
    · rw [h₁.1.1, h₂.1.1, kx.reg ky (by decide)]
    · rw [h₁.1.2, h₂.1.2, kx.reg ky (by decide)]
    all_goals exact ev _ (by simp)

theorem loadC_rel : RelCT isa (Two (SG M1)) loadC (Two (SG M2)) := by
  unfold loadC
  refine cutW (Y := YC) (X' := M2) (fun s0 s h => ?_) (fun _ _ h => loadCS h)
    (two_taint _ (pins_fr fun _ _ h => h.ctx.fr) (by taint_decide))
    (toPost (wk (fun _ _ _ _ h => h.1) (two_taint _ pins_YC (by taint_decide))))
  have hf := h.ctx.fr
  have ev := EVs.of_env h.env
  refine ldf_wp hf (by decide) (by decide) (ldf_wp (hf.write (by decide) _) (by decide) (by decide) (WP.block_nil ?_))
  refine ⟨⟨?_, ?_⟩, (ev.write (by decide) _).write (by decide) _, ?_⟩
  · rw [gpr_write_of_ne _ _ (by decide), gpr_write_self, hf.wRand]
  · rw [gpr_write_self, mem_write, hf.wOutLen]
  · rw [gpr_write_of_ne _ _ (by decide), gpr_write_of_ne _ _ (by decide), hf.s11]

/-- After `closeCheck`'s load of `p_len`. -/
def YP (s0 t : State) : Prop :=
  (Fr s0 t ∧ Env t (stackArg s0 1) (8 * sL s0) (cw s0)) ∧ t.gpr .t2 = s0.gpr .a6

/-- After `loadP`'s first block. -/
def YQ (s0 t : State) : Prop :=
  (t.gpr .s7 = s0.gpr .a5 ∧ t.gpr .s8 = s0.gpr .a1) ∧
    t.gpr .a7 = off (stackArg s0 1) (slot (cw s0) VG.Impl.RsaKeyGen.RISCV64.Candidate.aP) ∧
    t.gpr .s5 = BitVec.ofNat 64 (8 * (cw s0 + 2)) ∧ t.gpr .t0 = BitVec.ofNat 64 (cw s0) ∧ t.gpr .s6 = stackArg s0 1

theorem keep_write (s : State) {r : Reg} (v : BitVec 64) : Keep [r] s (s.write r v) :=
  ⟨fun r' hr => gpr_write_of_ne _ _ (by simpa using hr), rfl, rfl⟩

theorem pins_YQ : Pins (SG YQ) [.s7, .s8, .a7, .t0, .s6, .s5] :=
  pins_by fun _ _ _ _ _ kx ky h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h₁.1.1, h₂.1.1, kx.reg ky (by decide)]
    · rw [h₁.1.2, h₂.1.2, kx.reg ky (by decide)]
    · rw [h₁.2.1, h₂.2.1, kx.arg ky (by decide), kx.cw ky]
    · rw [h₁.2.2.2.1, h₂.2.2.2.1, kx.cw ky]
    · rw [h₁.2.2.2.2, h₂.2.2.2.2, kx.arg ky (by decide)]
    · rw [h₁.2.2.1, h₂.2.2.1, kx.cw ky]

theorem pins_PA {X : State → State → Prop} (hx : ∀ s0 t, X s0 t → Fr s0 t ∧ Env t (stackArg s0 1) (8 * sL s0) (cw s0)) :
    Pins (SG X) [.s11, .s6, .s5, .t0, .a7] :=
  pins_by fun _ _ _ _ _ kx ky h₁ h₂ r hr => by
    have ev := EVs.agree kx ky (EVs.of_env (hx _ _ h₁).2) (EVs.of_env (hx _ _ h₂).2)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [(hx _ _ h₁).1.s11, (hx _ _ h₂).1.s11, kx.fb ky]
    all_goals exact ev _ (by simp)

theorem calc_rel {X : State → State → Prop}
    (hx : ∀ s0 t, X s0 t → (Fr s0 t ∧ Env t (stackArg s0 1) (8 * sL s0) (cw s0)) ∧
      WP isa (seqs closeCalc) t fun _ => True) :
    RelCT isa (Two (SG X)) (seqs closeCalc) fun _ _ => True := by
  show RelCT isa _ (.seq (.seq (.block loadPA) (.seq VG.Impl.Bignum.RISCV64.Precompute.loadN
    (.block [.addi .a7 .s6 VG.Impl.Bignum.hdrBytes]))) (seqs (closeCalc.drop 1))) _
  exact relCT_assocR (cutW (Y := YQ) (X' := fun _ _ => True) (fun _ _ h => loadPA_ok (hx _ _ h).1.1 (hx _ _ h).1.2)
    (fun _ _ h => WP.assoc (hx _ _ h).2) (two_taint _ (pins_PA fun _ _ h => (hx _ _ h).1) (by taint_decide))
    (wk (fun _ _ _ _ h => h.1) (two_taint _ pins_YQ (by taint_decide))))

theorem close_rel : RelCT isa (Two (SG M2)) closeCheck (Two (SG M3)) := by
  unfold closeCheck
  refine cutW (Y := YP) (X' := M3) (fun s0 s h => ?_) (fun _ _ h => closeS h)
    (two_taint _ (pins_fr fun _ _ h => h.ctx.fr) (by taint_decide))
    (toPost (iteK (fun a s₁ s₂ ⟨x, kx, _, h₁⟩ ⟨y, ky, _, h₂⟩ => by
        rw [VG.RISCV64.Steps.eval_zero, VG.RISCV64.Steps.eval_zero, h₁, h₂, kx.reg ky (by decide)])
      (two_taint [] pins_nil (by taint_decide))
      (calc_rel fun _ _ h => ⟨h.1.1.1, WP.mono h.2 fun _ _ => trivial⟩)))
  have hf := h.ctx.fr
  refine ldf_wp hf (by decide) (by decide) (WP.block_nil ⟨⟨hf.write (by decide) _, h.env.keep (keep_write _ _)
    (by decide)⟩, ?_⟩)
  rw [gpr_write_self, hf.wPLen]

/-! ### `gcdCheck` -/

section
open VG.Impl.Bignum.RISCV64 (countLoop)

/-- `e` in `s10`, and `Env`'s registers. -/
def Y6 (s0 t : State) : Prop := t.gpr .s10 = BitVec.ofNat 64 (eV s0) ∧ EVs s0 t

/-- `loadE`'s loop and its move into `s10`. -/
abbrev loadE2 : Prog isa :=
  .seq (countLoop .t5 [.shift .sll .d .t2 .t2 8, .load .b .t4 .t3 0, .add .t2 .t2 .t4, .addi .t3 .t3 1])
    (.block [.addi .s10 .t2 0])

/-- After `loadE`'s loads of `e` and `e_len`. -/
def Y5 (s0 t : State) : Prop := (t.gpr .t3 = s0.gpr .a3 ∧ t.gpr .t5 = s0.gpr .a4) ∧ WP isa loadE2 t (Y6 s0)

/-- After `e`'s low bit. -/
def Y7 (s0 t : State) : Prop := t.gpr .t2 = BitVec.ofNat 64 (eV s0) &&& BitVec.ofInt 64 1 ∧ Y6 s0 t

/-- After `e − 1`. -/
def Y8 (s0 t : State) : Prop := t.gpr .t2 = BitVec.ofNat 64 (eV s0) + BitVec.ofInt 64 (-1) ∧ EVs s0 t

/-- `gcdCheck` from the state before it. -/
def X0 (s0 t : State) : Prop :=
  M3 s0 t ∧ Spec.RsaKeyGen.tooClose (64 * cw s0) (Spec.RsaKeyGen.otherPrime (pB s0)) (candOf s0) = false

theorem eA_ok {s0 s : State} (hf : Fr s0 s) :
    WP isa (.block [.li .t2 0, ldf .t3 oE, ldf .t5 oELen]) s fun t =>
      t.gpr .t3 = s0.gpr .a3 ∧ t.gpr .t5 = s0.gpr .a4 := by
  refine WP.block_cons_iff.mpr ⟨_, exec_li (imm := 0) (by decide), ?_⟩
  have h1 := hf.write (r := .t2) (by decide) (BitVec.ofInt 64 0)
  refine ldf_wp h1 (by decide) (by decide) (ldf_wp (h1.write (by decide) _) (by decide) (by decide) (WP.block_nil ?_))
  refine ⟨?_, ?_⟩
  · rw [gpr_write_of_ne _ _ (by decide), gpr_write_self, mem_write, hf.wE]
  · rw [gpr_write_self, mem_write, mem_write, hf.wELen]

theorem gcd_rel0 : RelCT isa (Two (SG X0)) gcdCheck fun _ _ => True := by
  show RelCT isa _ (.seq (.seq (.block [.li .t2 0, ldf .t3 oE, ldf .t5 oELen]) loadE2) _) _
  refine relCT_assocR (cutW (Y := Y5) (X' := fun _ _ => True) (fun s0 s ⟨h, _⟩ => ?_)
    (fun _ _ ⟨h, ncl⟩ => WP.mono (WP.assoc (gcdS h ncl)) fun _ _ => trivial)
    (two_taint _ (pins_fr fun _ _ h => h.1.ctx.fr) (by taint_decide))
    (cutW (Y := Y6) (X' := fun _ _ => True) (fun _ _ h => h.1.2) (fun _ _ h => h.2)
      (wk (fun _ _ _ _ h => h.1.1)
        (two_taint _ (pins_args (by decide) (by decide) (by decide) fun _ _ h => h) (by taint_decide)))
      (cutW (Y := Y7) (X' := fun _ _ => True) (fun s0 t ⟨⟨h10, ev⟩, _⟩ => ?_) (fun _ _ h => h.2)
        (two_taint [] pins_nil (by taint_decide))
        (iteK (fun a s₁ s₂ ⟨x, kx, h₁⟩ ⟨y, ky, h₂⟩ => by
            rw [VG.RISCV64.Steps.eval_zero, VG.RISCV64.Steps.eval_zero, h₁.1, h₂.1, kx.eV ky])
          (two_taint [] pins_nil (by taint_decide))
          (cutW (Y := Y8) (X' := fun _ _ => True) (fun s0 t ⟨⟨⟨_, h10, ev⟩, _⟩, _⟩ => ?_) (fun _ _ h => h.2)
            (two_taint [] pins_nil (by taint_decide))
            (iteK (fun a s₁ s₂ ⟨x, kx, h₁⟩ ⟨y, ky, h₂⟩ => by
                rw [VG.RISCV64.Steps.eval_zero, VG.RISCV64.Steps.eval_zero, h₁.1, h₂.1, kx.eV ky])
              (two_taint [] pins_nil (by taint_decide))
              (wk (fun _ _ _ _ h => h.1.1.2) (two_taint _ (pins_ev fun _ _ h => h) (by taint_decide)))))))))
  · have hf := h.ctx.fr
    have ev := EVs.of_env h.env
    exact WP.and (eA_ok hf) (WP.seq_iff.mp (WP.mono (loadE_ok hf) fun _ ⟨⟨h10, _⟩, k⟩ =>
      ⟨h10, EVs.of_env (h.env.keep k (by decide))⟩))
  · refine WP.block_cons_iff.mpr ⟨_, exec_logicImm (op := .and) (d := .t2) (n := .s10) (imm := 1) (by decide),
      WP.block_nil ⟨?_, ?_, ev.write (r := .t2) (by decide) _⟩⟩
    · simp only [gpr_write_self, h10]
    · rw [gpr_write_of_ne _ _ (by decide), h10]
  · refine WP.block_cons_iff.mpr ⟨_, exec_addi (d := .t2) (n := .s10) (imm := -1) (by decide),
      WP.block_nil ⟨?_, ev.write (r := .t2) (by decide) _⟩⟩
    rw [gpr_write_self, h10]

theorem gcd_rel : RelCT isa (Two (SG X0)) gcdCheck (Two (SG M4)) :=
  two_post gcd_rel0 fun _ _ ⟨s0, k, h, ncl⟩ => WP.mono (gcdS h ncl) fun _ ht => ⟨s0, k, ht⟩

end

end VG.Proof.RsaKeyGen.RISCV64.Cand

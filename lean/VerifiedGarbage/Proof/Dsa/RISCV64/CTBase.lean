module

public import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyFront
public import VerifiedGarbage.Proof.Dsa.RISCV64.CheckKey
public import VerifiedGarbage.Impl.Dsa.RISCV64.Sign
public import VerifiedGarbage.Proof.Dsa.DomainShape
public import VerifiedGarbage.Proof.Bignum.RISCV64.Reach
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
meta import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyFront
meta import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyFn
meta import VerifiedGarbage.Proof.Dsa.RISCV64.CheckKey
meta import VerifiedGarbage.Impl.Dsa.RISCV64.Sign
meta import VerifiedGarbage.Proof.Dsa.DomainShape
meta import VerifiedGarbage.Proof.Bignum.RISCV64.Reach
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyFn
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
meta import VerifiedGarbage.Proof.Dsa.PackedBytes
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA verification on RISC-V: constant time, the relation of two runs

The taint analysis treats memory as secret (`Proof/Framework/RISCV64/Taint.lean`),
but this code keeps only `S` (`s6`), the key (`s11`) and the signature (`ra`) in
registers: the lengths (the header's word `hLens`) and the digest's address
(`hDigest`) are loaded from memory again wherever they are used, and the checks
of the key branch on values computed from the key's public bytes. Both are the
same in two runs for the same public data `VD` (the layout, the pointers, the
digest's length and the key's public bytes), as in RSA's RISC-V proofs
(`Proof/Bignum/RISCV64/Reach.lean`): a program's list of programs
(`Code.flat`) is cut after each block that loads such words, and at the cuts
the registers the taint analysis needs public have values that the public data
fixes (`pins_at_fix`), by correctness.

A branch on a value of the key's public part (`andThen`'s `ite` on `a0`) is an
element of its list: both runs take the same side (`zero_at`), and each side is
a *level* of its own, its list cut again, from the states `At Φ F n` of the
parent with the condition (`rel_ite_at`). A level's states are states of a run
from the start, so they terminate (`run_ite`) and satisfy what correctness says
of them (`at_sem`).

## The cuts

Each level's list, with its cuts (the indices of `At`) and its branches
(`CTKey.lean`, `CTParams.lean`, `CTBody*.lean`, assembled in `VerifyCT.lean`):

* `verify` (`FT`, from `C0`): `entry` is split after its first two
  instructions, which load `scratch`'s address from the stack (`entry_rel`);
  cuts at 1 (after `entry`: `S`, the key and the signature), 2 (after `ptrP`),
  4 (after p's `sigLen`, for `topBit`'s address), the branch on p's top bit at
  5 (level `X1`), and 6 (before `restore`: no instruction of the checks or of
  `body` writes `s6`);
* `X1`: cuts at 0, 2 (after `ptrQ`) and 4 (after q's `sigLen`), the branch on
  q's top bit at 5 (`X2`);
* `X2`: cut at 0 (the scans' results, for `pairs`), the branch on the sizes at
  12 (`R0`);
* `R0`, `R1`: their one block (`ptrP ++ odd`, `ptrQ ++ odd`) split after the
  pointer (`rel_ptr`), the branch on p's or q's oddness at 1 (`R1`, `R2`);
* `R2`: cuts at 0, 2 (after `enterQ; ptrQ`) and 10 (after `getP s10`), the
  branch on `p mod q` at 23 (`R3`);
* `R3`: cuts at 0, 2 (after `enterP; ptrP`) and 18 (after `ptrG`), the branch
  on g's range at 45 (level `elemOrder`, cut at 0 and 3, after its `ptrQ`), and
  on g's check at 46 (`RK`);
* `RK`: cuts at 0 and 1 (after `ptrY`), the branch on y's range at 28
  (`elemOrder`) and on y's check at 29 (`body`);
* `body` (`FB`): cuts at 0 and after each of its 17 blocks that load the
  header's words (1, 9, 50, 53, 63, 104, 106, 108, 154, 157, 161, 171, 215,
  225, 288, 291, 297). `scalarLen`'s and `scalar`'s branches are on registers
  those cuts fix, which the taint analysis checks.

Between the cuts the registers fixed are always `S`, the key and the
signature (`fixB`), the working space's registers (`envP`, `envQ`) and those
the last block loaded; the failing side of each check is `li a0 0`.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.CT

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Proof.Dsa.RISCV64
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post two_taint)
open VG.Proof.Dsa (significant)

variable {α : Type}

/-! ## Levels -/

/-- What correctness says of the states after the first `n` programs. -/
theorem at_sem {Φ : α → State → Prop} {F : List (Prog isa)} {n : Nat} {M : α → State → Prop}
    (hw : ∀ a s, Φ a s → WP isa (Code.seqL (F.take n)) s (M a)) {a : α} {u : State} (h : At Φ F n a u) :
    M a u := by
  obtain ⟨s₀, t, h₀, e⟩ := h
  obtain ⟨_, _, e', hm⟩ := hw a s₀ h₀
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact hm

/-- The registers of `ps` hold their values. -/
def Fix : List (Reg × BitVec 64) → State → Prop
  | [], _ => True
  | p :: ps, s => s.gpr p.1 = p.2 ∧ Fix ps s

theorem Fix.get : ∀ {ps : List (Reg × BitVec 64)} {s : State}, Fix ps s → ∀ p ∈ ps, s.gpr p.1 = p.2
  | [], _, _, _, h => absurd h List.not_mem_nil
  | _ :: _, _, ⟨h₁, h₂⟩, _, hm => by
    rcases List.mem_cons.mp hm with rfl | hm
    · exact h₁
    · exact Fix.get h₂ _ hm

theorem Fix.app : ∀ {l₁ l₂ : List (Reg × BitVec 64)} {s : State}, Fix l₁ s → Fix l₂ s → Fix (l₁ ++ l₂) s
  | [], _, _, _, h => h
  | _ :: _, _, _, ⟨h₁, h₂⟩, h => ⟨h₁, Fix.app h₂ h⟩

theorem pins_fix {Ψ : α → State → Prop} (ps : α → List (Reg × BitVec 64)) {rs : List Reg}
    (hrs : ∀ a, (ps a).map Prod.fst = rs) (h : ∀ a u, Ψ a u → Fix (ps a) u) : Pins Ψ rs := by
  intro a s₁ s₂ h₁ h₂ r hr
  rw [← hrs a] at hr
  obtain ⟨p, hm, rfl⟩ := List.mem_map.mp hr
  rw [(h a s₁ h₁).get p hm, (h a s₂ h₂).get p hm]

/-- The registers a cut fixes, from values of the public data. -/
theorem pins_at_fix {Φ : α → State → Prop} {F : List (Prog isa)} {n : Nat} (ps : α → List (Reg × BitVec 64))
    {rs : List Reg} (hrs : ∀ a, (ps a).map Prod.fst = rs)
    (hw : ∀ a s, Φ a s → WP isa (Code.seqL (F.take n)) s (Fix (ps a))) : Pins (At Φ F n) rs :=
  pins_fix ps hrs fun _ _ h => at_sem hw h

/-- The states of a cut of another list with the same first `n` programs, from
states of a stronger predicate. -/
theorem at_mono {Φ Ψ : α → State → Prop} {F F' : List (Prog isa)} {n : Nat} (hΦ : ∀ a s, Ψ a s → Φ a s)
    (hF : F'.take n = F.take n) {a : α} {u : State} (h : At Ψ F' n a u) : At Φ F n a u :=
  let ⟨s₀, t, h₀, e⟩ := h
  ⟨s₀, t, hΦ a s₀ h₀, hF ▸ e⟩

theorem pins_mono {Φ Ψ : α → State → Prop} {rs : List Reg} (h : Pins Φ rs) (hΨ : ∀ a s, Ψ a s → Φ a s) :
    Pins Ψ rs :=
  fun a _ _ h₁ h₂ => h a _ _ (hΨ a _ h₁) (hΨ a _ h₂)

/-- A fact of the public data, from the level's states. -/
theorem at_pure {Φ : α → State → Prop} {F : List (Prog isa)} {n : Nat} {G : α → Prop} (hG : ∀ a s, Φ a s → G a)
    {a : α} {u : State} (h : At Φ F n a u) : G a :=
  let ⟨s₀, _, h₀, _⟩ := h
  hG a s₀ h₀

/-- Both runs agree whether `r` is zero at a cut where it is zero exactly when
the public data satisfies `C`. -/
theorem zero_at {Φ : α → State → Prop} {F : List (Prog isa)} {n : Nat} {r : Reg} (C : α → Prop)
    (hw : ∀ a s, Φ a s → WP isa (Code.seqL (F.take n)) s fun u => (u.gpr r = 0 ↔ C a)) :
    ∀ a s₁ s₂, At Φ F n a s₁ → At Φ F n a s₂ → (s₁.gpr r == 0) = (s₂.gpr r == 0) := by
  intro a s₁ s₂ h₁ h₂
  have e₁ := at_sem hw h₁
  have e₂ := at_sem hw h₂
  by_cases hc : C a
  · rw [beq_iff_eq.mpr (e₁.mpr hc), beq_iff_eq.mpr (e₂.mpr hc)]
  · rw [show (s₁.gpr r == 0) = false from by simpa using fun e => hc (e₁.mp e),
      show (s₂.gpr r == 0) = false from by simpa using fun e => hc (e₂.mp e)]

/-- A branch of the list on a register both runs agree is zero or not: each
side from the states of the cut with its condition. -/
theorem rel_ite_at {Φ : α → State → Prop} {F : List (Prog isa)} {n : Nat} {r : Reg} {t e : Prog isa}
    (hF : (F.drop n).take 1 = [.ite (.zero r) t e])
    (hz : ∀ a s₁ s₂, At Φ F n a s₁ → At Φ F n a s₂ → (s₁.gpr r == 0) = (s₂.gpr r == 0))
    (ht : RelCT isa (Two fun a u => At Φ F n a u ∧ u.gpr r = 0) t fun _ _ => True)
    (he : RelCT isa (Two fun a u => At Φ F n a u ∧ u.gpr r ≠ 0) e fun _ _ => True) :
    RelCT isa (Two (At Φ F n)) (seg F n (n + 1)) fun _ _ => True := by
  show RelCT isa _ (Code.seqL ((F.drop n).take (n + 1 - n))) _
  rw [Nat.add_sub_cancel_left, hF]
  refine VG.Proof.Bignum.RISCV64.RelCT.seqL_single (RelCT.ite (fun s₁ s₂ ⟨a, h₁, h₂, _⟩ => by
    rw [Steps.eval_zero, Steps.eval_zero, hz a _ _ h₁ h₂]) ?_ ?_)
  · refine ht.mono (fun s₁ s₂ ⟨⟨a, h₁, h₂, hsp⟩, hc⟩ => ?_) fun _ _ h => h
    rw [Steps.eval_zero, Option.some.injEq, beq_iff_eq] at hc
    have hc₂ : (s₂.gpr r == 0) = true := by rw [← hz a _ _ h₁ h₂, hc, beq_self_eq_true]
    exact ⟨a, ⟨h₁, hc⟩, ⟨h₂, beq_iff_eq.mp hc₂⟩, hsp⟩
  · refine he.mono (fun s₁ s₂ ⟨⟨a, h₁, h₂, hsp⟩, hc⟩ => ?_) fun _ _ h => h
    rw [Steps.eval_zero, Option.some.injEq] at hc
    have hc₂ : (s₂.gpr r == 0) = false := by rw [← hz a _ _ h₁ h₂, hc]
    exact ⟨a, ⟨h₁, fun e => by rw [e] at hc; exact absurd hc (by decide)⟩,
      ⟨h₂, fun e => by rw [e] at hc₂; exact absurd hc₂ (by decide)⟩, hsp⟩

/-- A branch of the list, run from a state of its cut. -/
theorem run_ite {Φ : α → State → Prop} {F : List (Prog isa)} {n : Nat} {c : Cond} {t e : Prog isa}
    (hrun : ∀ a s, Φ a s → WP isa (Code.seqL F) s fun _ => True)
    (hF : (F.drop n).take 1 = [.ite c t e]) {a : α} {u : State} (h : At Φ F n a u) :
    WP isa (.ite c t e) u fun _ => True := by
  have h' := at_step hrun (Nat.le_succ n) h
  have hs : seg F n (n + 1) = Code.seqL [.ite c t e] := by
    show Code.seqL ((F.drop n).take (n + 1 - n)) = _
    rw [Nat.add_sub_cancel_left, hF]
  rw [hs] at h'
  obtain ⟨_, _, e', -⟩ := h'
  cases e' with
  | seq x _ => exact ⟨_, _, x, trivial⟩

/-- A level: the side of a branch on `r = 0` that it takes, as a list. -/
theorem run_then {Φ : α → State → Prop} {F : List (Prog isa)} {n : Nat} {r : Reg} {t e : Prog isa}
    (hrun : ∀ a s, Φ a s → WP isa (Code.seqL F) s fun _ => True)
    (hF : (F.drop n).take 1 = [.ite (.zero r) t e]) :
    ∀ a u, (At Φ F n a u ∧ u.gpr r = 0) → WP isa (Code.seqL t.flat) u fun _ => True :=
  fun _ _ ⟨h, hz⟩ => WP.of_flat rfl (WP.ite_true (run_ite hrun hF h) (by rw [Steps.eval_zero, hz]; rfl))

/-- `fail`: 0 into `a0`. -/
theorem fail_rel {Ψ : α → State → Prop} : RelCT isa (Two Ψ) (.block [.li .a0 0]) fun _ _ => True :=
  two_taint [] (fun _ _ _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide)

theorem nil_rel {P : State → State → Prop} : RelCT isa P (.block []) fun _ _ => True :=
  RelCT.block_nil fun _ _ _ => trivial

/-! ## The public data -/

/-- A call's public data: the layout, the key, the signature, the digest, its
length and the key's public octets. -/
structure VD where
  L : Lay
  key : Addr
  sig : Addr
  dig : Addr
  dl : Nat
  kb : List Byte
  /-- The key's public octets, `kb`'s: p||q||g, then y for a key, and x when signing. -/
  kn : Nat
  /-- The octets at `sig`: the signature's, the nonce's, x's, or none. -/
  sgl : Nat
  /-- Whether the header keeps the digest's address. -/
  full : Bool
  /-- `out`, which the header's word `hOut` keeps, when signing or deriving. -/
  out : Option Addr

namespace VD

/-- The digest's length the code uses: at most 64 octets. -/
abbrev d (v : VD) : Nat := min v.dl 64

/-- The key's octets from `o`, `k` of them. -/
def sl (v : VD) (o k : Nat) : List Byte := (v.kb.drop o).take k

def pB (v : VD) : List Byte := v.sl 0 v.L.pl
def qB (v : VD) : List Byte := v.sl v.L.pl v.L.ql
def p (v : VD) : Nat := Spec.Dsa.decodeBE v.pB
def q (v : VD) : Nat := Spec.Dsa.decodeBE v.qB
def g (v : VD) : Nat := Spec.Dsa.decodeBE (v.sl (v.L.pl + v.L.ql) v.L.pl)
def y (v : VD) : Nat := Spec.Dsa.decodeBE (v.sl (2 * v.L.pl + v.L.ql) v.L.pl)

/-- The scans of p's and q's octets: significant octets, and the first one. -/
def sP (v : VD) : Nat := (significant v.pB).1
def tP (v : VD) : Nat := (significant v.pB).2.toNat
def sQ (v : VD) : Nat := (significant v.qB).1
def tQ (v : VD) : Nat := (significant v.qB).2.toNat

/-- q's significant octets, as the header keeps them. -/
def qb (v : VD) : Nat := Spec.Dsa.bitLength v.q / 8

end VD

/-- What every state from the entry on satisfies, for the public data `v`. -/
structure Base (v : VD) (s : State) : Prop where
  ok : v.L.Ok
  regs : Regs s v.L v.key v.sig
  scr : ScrL s v.L
  hk : Src s v.L v.key v.kn
  hsg : Src s v.L v.sig v.sgl
  hdg : Src s v.L v.dig v.d
  kb : Spec.Rsa.bytesAt s.mem v.key v.kn = v.kb
  kn : 2 * v.L.pl + v.L.ql ≤ v.kn
  dig8 : v.full = true → word s.mem v.L.S hDigest = v.dig
  hout : ∀ o ∈ v.out, word s.mem v.L.S Sign.hOut = o

theorem Base.step {v : VD} {s t : State} (h : Base v s) (hr : Regs t v.L v.key v.sig) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) (ho : Outside v.L.S 0 v.L.Z s.mem t.mem)
    (h8 : word t.mem v.L.S hDigest = word s.mem v.L.S hDigest)
    (h24 : word t.mem v.L.S Sign.hOut = word s.mem v.L.S Sign.hOut) : Base v t :=
  ⟨h.ok, hr, h.scr.congr hwr, h.hk.keep hrd hwr, h.hsg.keep hrd hwr, h.hdg.keep hrd hwr,
    (h.hk.bytes ho (by omega)).trans h.kb, h.kn, fun hf => h8.trans (h.dig8 hf),
    fun o ho => h24.trans (h.hout o ho)⟩

/-- `Base` through code that keeps its registers and changes memory only in
`Kept`'s places. -/
theorem Base.kept {v : VD} {s t : State} {rs : List Reg} (h : Base v s) (k : Keep rs s t)
    (hk : Kept v.L s.mem t.mem) (hr : Regs t v.L v.key v.sig) : Base v t :=
  h.step hr k.2.1 k.2.2 hk.out (hk.word (Or.inl (by decide)))
    (hk.word (Or.inr ⟨by simp only [hLens, Sign.hOut]; omega, by simp only [Sign.hOut]; omega⟩))

/-- `Base` through code that keeps its registers and changes memory only in
the body. -/
theorem Base.body {v : VD} {s t : State} {rs : List Reg} (h : Base v s) (k : Keep rs s t)
    (hb : Body v.L s.mem t.mem) (hr : ∀ r ∈ regsRegs, r ∉ rs := by decide) : Base v t :=
  h.kept k (Kept.ofBody h.ok hb) (h.regs.keep k hb hr)

/-- `Base` through code that keeps its registers and memory. -/
theorem Base.keepM {v : VD} {s t : State} {rs : List Reg} (h : Base v s) (k : Keep rs s t)
    (hm : t.mem = s.mem) (hr : ∀ r ∈ regsRegs, r ∉ rs := by decide) : Base v t :=
  h.body k (by rw [hm]; exact Body.refl _ _) hr

theorem Base.bytes {v : VD} {s : State} (h : Base v s) {o k : Nat} (hk : o + k ≤ v.kn) :
    Spec.Rsa.bytesAt s.mem (off v.key o) k = v.sl o k := by
  rw [VD.sl, ← h.kb, VG.Proof.Dsa.bytesAt_slice s.mem v.key hk]

theorem Base.bytesP {v : VD} {s : State} (h : Base v s) : Spec.Rsa.bytesAt s.mem v.key v.L.pl = v.pB := by
  have := h.bytes (o := 0) (k := v.L.pl) (by have := h.kn; omega)
  rwa [off, BitVec.add_zero] at this

theorem Base.bytesQ {v : VD} {s : State} (h : Base v s) :
    Spec.Rsa.bytesAt s.mem (off v.key v.L.pl) v.L.ql = v.qB :=
  h.bytes (by have := h.kn; omega)

theorem Base.p {v : VD} {s : State} (h : Base v s) : pOf s.mem v.L v.key = v.p := by
  rw [pOf, h.bytesP]; rfl

theorem Base.q {v : VD} {s : State} (h : Base v s) : qOf s.mem v.L v.key = v.q := by
  rw [qOf, h.bytesQ]; rfl

theorem Base.g {v : VD} {s : State} (h : Base v s) : gOf s.mem v.L v.key = v.g := by
  rw [gOf, h.bytes (by have := h.kn; omega)]; rfl

/-- The public octets name y. -/
abbrev KY (v : VD) : Prop := 3 * v.L.pl + v.L.ql ≤ v.kn

theorem Base.y {v : VD} {s : State} (h : Base v s) (hy : KY v) : yOf s.mem v.L v.key = v.y := by
  rw [yOf, h.bytes (by omega)]; rfl

/-- The header's lengths, with `qb` as q's significant octets. -/
abbrev Lens (v : VD) (qb : Nat) (s : State) : Prop := word s.mem v.L.S hLens = pack v.L.pl v.L.ql qb v.d

/-- The registers `S`, the key and the signature. -/
abbrev fixB (v : VD) : List (Reg × BitVec 64) := [(.s6, v.L.S), (.s11, v.key), (.ra, v.sig)]

theorem Base.fixB {v : VD} {s : State} (h : Base v s) : Fix (fixB v) s :=
  ⟨h.regs.s6, h.regs.s11, h.regs.ra, trivial⟩

theorem Base.pl {v : VD} {s : State} (h : Base v s) : 128 ≤ v.L.pl ∧ v.L.pl ≤ 384 := by
  rcases h.ok.pl with e | e | e <;> omega

theorem Base.ql {v : VD} {s : State} (h : Base v s) : 20 ≤ v.L.ql ∧ v.L.ql ≤ 32 := by
  rcases h.ok.ql with e | e | e <;> omega

/-- The P space's registers. -/
abbrev envP (v : VD) : List (Reg × BitVec 64) :=
  [(.a7, off v.L.S (VG.Proof.Bignum.slot v.L.wp 0)), (.s5, BitVec.ofNat 64 (8 * (v.L.wp + 2))),
    (.t0, BitVec.ofNat 64 v.L.wp)]

/-- The Q space's registers. -/
abbrev envQ (v : VD) : List (Reg × BitVec 64) :=
  [(.a7, off v.L.Q (VG.Proof.Bignum.slot v.L.wq 0)), (.s5, BitVec.ofNat 64 (8 * (v.L.wq + 2))),
    (.t0, BitVec.ofNat 64 v.L.wq)]

theorem fix_envP {v : VD} {s : State} (h : InP s v.L) : Fix (envP v) s := ⟨h.env.a7, h.env.s5, h.env.t0, trivial⟩

theorem fix_envQ {v : VD} {s : State} (h : InQ s v.L) : Fix (envQ v) s := ⟨h.env.a7, h.env.s5, h.env.t0, trivial⟩

/-! ## The entry -/

/-- A call's public data. -/
def vdOf (s : State) : VD :=
  ⟨layOf s, s.gpr .a0, s.gpr .a4, s.gpr .a6, (s.gpr .a7).toNat,
    Spec.Rsa.bytesAt s.mem (s.gpr .a0) (3 * (s.gpr .a2).toNat + (s.gpr .a3).toNat),
    3 * (s.gpr .a2).toNat + (s.gpr .a3).toNat, 2 * (s.gpr .a3).toNat, true, none⟩

/-- On entry. -/
def C0 (v : VD) (s : State) : Prop := vContract.pre s ∧ vdOf s = v

/-- After the entry: the header's lengths with no `qb` yet. -/
abbrev P0 (v : VD) (s : State) : Prop := Base v s ∧ Lens v 0 s

/-- The contract's buffers are apart from `scratch`. -/
theorem pre_src {s : State} {A : Addr} {n k : Nat} (hm : (⟨A, n⟩ : Region) ∈ s.rd)
    (hd : (⟨A, n⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩) (_hnw : A.toNat + n ≤ 2 ^ 64)
    (hn : n < 2 ^ 64) (hk : k ≤ n) {t : State} (hr : t.rd = s.rd) (hw : t.wr = s.wr) : Src t (layOf s) A k :=
  ⟨fun i hi => ⟨_, by rw [hr, hw]; exact List.mem_append_left _ hm,
    Offset.contains_base _ (by omega_arith) (by omega_arith)⟩,
    fun i hi => Pub.ne_of_disjoint hd (by omega_arith) i (by omega_arith)⟩

/-- `entry` leaves `P0`. -/
theorem front_P0 {v : VD} {s : State} (h : C0 v s) : WP isa (.block Verify.entry) s (P0 v) := by
  obtain ⟨hp, rfl⟩ := h
  have hL := layOf_ok hp
  have hZ := hL.z256
  have hpre := hp
  obtain ⟨hrd, -, dKS, dGS, dDS, -, nwK, nwG, nwD, -, -, hkl, hsl, -, -, -⟩ := hp
  refine WP.mono (front_ok hpre) fun t ⟨F, k⟩ => ?_
  have hK : ∀ {u : State}, u.rd = s.rd → u.wr = s.wr →
      Src u (layOf s) (s.gpr .a0) (3 * (layOf s).pl + (layOf s).ql) :=
    fun hr hw => pre_src (A := s.gpr .a0) (by rw [hrd]; simp) dKS nwK (s.gpr .a1).isLt
      (by simp only [layOf]; omega_arith) hr hw
  refine ⟨⟨hL, F.regs, F.scr, hK k.2.1 k.2.2,
    pre_src (A := s.gpr .a4) (by rw [hrd]; simp) dGS nwG (s.gpr .a5).isLt (by simp only [vdOf, layOf]; omega_arith)
      k.2.1 k.2.2,
    pre_src (A := s.gpr .a6) (by rw [hrd]; simp) dDS nwD (s.gpr .a7).isLt (Nat.min_le_left _ _) k.2.1 k.2.2,
    ((hK rfl rfl).bytes F.out (by simp only [layOf] at hZ ⊢; omega)), by simp only [vdOf, layOf]; omega,
    fun _ => F.dig, fun _ h => nomatch h⟩, F.lens⟩

/-- After loading `scratch`'s address. -/
def L1 (v : VD) (s : State) : Prop := s.gpr .t2 = v.L.S

theorem loadS_L1 {v : VD} {s : State} (h : C0 v s) :
    WP isa (.block [.addSp .t2 0, .load .d .t2 .t2 0]) s (L1 v) := by
  obtain ⟨hp, rfl⟩ := h
  obtain ⟨hrd, -, -, -, -, -, -, -, -, -, -, -, -, -, -, sp16⟩ := hp
  have hst' : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 0) 8 := by
    have : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8 :=
      ⟨stackArgs s, List.mem_append_left _ (by rw [hrd]; simp), by simp [Region.Contains]⟩
    simpa only [stackArgAddr] using this
  have hsa : (s.sp + BitVec.ofNat 64 0).toNat % 8 = 0 := by rw [add_ofNat_zero]; omega
  have hv : s.mem.readW (s.sp + BitVec.ofNat 64 0) 64 = stackArg s 0 := by simp [stackArg, stackArgAddr]
  have first : WP isa (.block [.addSp .t2 0, .load .d .t2 .t2 0]) s fun s₁ => s₁ = s.write .t2 (stackArg s 0) := by
    brun [exec_addSp (show 0 < 2048 by decide), hst', hsa, hv, write_write]
  exact WP.mono first fun s₁ e => by rw [e]; exact gpr_write_self _ _ _

theorem pins_L1 : Pins L1 [.t2] := by
  intro v s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  rw [h₁, h₂]

theorem entry_rel : RelCT isa (Two C0) (.block Verify.entry) fun _ _ => True := by
  unfold Verify.entry
  rw [List.append_assoc]
  refine RelCT.block_append (M := isa) (l₁ := ([.addSp .t2 0, .load .d .t2 .t2 0] : List Instr)) ?_
  exact RelCT.seq (two_post (two_taint [] (fun _ _ _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide))
    fun _ _ h => loadS_L1 h) (two_taint _ pins_L1 (by taint_decide))

/-! ## The levels -/

/-- The failing side of the checks. -/
abbrev fail0 : Prog isa := .block [.li .a0 0]

/-- After g's check: y's, then `body`. -/
abbrev RK : Prog isa := andThen (.seq (.block ptrY) checkElem) Verify.body fail0
/-- After `p mod q = 1`: the P space, then g's check. -/
abbrev R3 : Prog isa := .seq setupP (andThen (.seq (.block ptrG) checkElem) RK fail0)
/-- After the oddness: `p mod q = 1`. -/
abbrev R2 : Prog isa := andThen pModQ R3 fail0
/-- After p's oddness: q's. -/
abbrev R1 : Prog isa := andThen (.block (ptrQ ++ odd)) R2 fail0
/-- After the sizes: p's oddness. -/
abbrev R0 : Prog isa := odds R2 fail0
/-- After q's top bit: q's significant octets into the header, and the pair of sizes. -/
abbrev X2 : Prog isa :=
  .seq (.block [.addi .a3 .a1 0, .shift .sll .d .t3 .a1 32, .load .d .t4 .s6 hLens, .add .t4 .t4 .t3,
    .store .d .t4 .s6 hLens]) (andThen pairs R0 fail0)
/-- After p's top bit: q's scan. -/
abbrev X1 : Prog isa := .seq (.block [.addi .a2 .a1 0]) (andThen (.seq (.block ptrQ) bytesBits) X2 fail0)

abbrev FT : List (Prog isa) := Code.flat Verify.verify
abbrev FX1 : List (Prog isa) := Code.flat X1
abbrev FX2 : List (Prog isa) := Code.flat X2
abbrev FR0 : List (Prog isa) := Code.flat R0
abbrev FR1 : List (Prog isa) := Code.flat R1
abbrev FR2 : List (Prog isa) := Code.flat R2
abbrev FR3 : List (Prog isa) := Code.flat R3
abbrev FK : List (Prog isa) := Code.flat RK
abbrev FE : List (Prog isa) := Code.flat elemOrder
abbrev FB : List (Prog isa) := Code.flat Verify.body

/-- The states of each level: those of its parent's cut, with the branch's condition. -/
abbrev ΦX1 (v : VD) (u : State) : Prop := At C0 FT 5 v u ∧ u.gpr .a0 = 0
abbrev ΦX2 (v : VD) (u : State) : Prop := At ΦX1 FX1 5 v u ∧ u.gpr .a0 = 0
abbrev ΦR0 (v : VD) (u : State) : Prop := At ΦX2 FX2 12 v u ∧ u.gpr .a0 = 0
abbrev ΦR1 (v : VD) (u : State) : Prop := At ΦR0 FR0 1 v u ∧ u.gpr .a0 = 0
abbrev ΦR2 (v : VD) (u : State) : Prop := At ΦR1 FR1 1 v u ∧ u.gpr .a0 = 0
abbrev ΦR3 (v : VD) (u : State) : Prop := At ΦR2 FR2 23 v u ∧ u.gpr .a0 = 0
abbrev ΦEg (v : VD) (u : State) : Prop := At ΦR3 FR3 45 v u ∧ u.gpr .a0 = 0
abbrev ΦK (v : VD) (u : State) : Prop := At ΦR3 FR3 46 v u ∧ u.gpr .a0 = 0
abbrev ΦEy (v : VD) (u : State) : Prop := At ΦK FK 28 v u ∧ u.gpr .a0 = 0
abbrev ΦB (v : VD) (u : State) : Prop := At ΦK FK 29 v u ∧ u.gpr .a0 = 0

theorem hFT : (FT.drop 5).take 1 = [.ite (.zero .a0) X1 fail0] := rfl
theorem hFX1 : (FX1.drop 5).take 1 = [.ite (.zero .a0) X2 fail0] := rfl
theorem hFX2 : (FX2.drop 12).take 1 = [.ite (.zero .a0) R0 fail0] := rfl
theorem hFR0 : (FR0.drop 1).take 1 = [.ite (.zero .a0) R1 fail0] := rfl
theorem hFR1 : (FR1.drop 1).take 1 = [.ite (.zero .a0) R2 fail0] := rfl
theorem hFR2 : (FR2.drop 23).take 1 = [.ite (.zero .a0) R3 fail0] := rfl
theorem hFR3g : (FR3.drop 45).take 1 = [.ite (.zero .a0) elemOrder (.block [])] := rfl
theorem hFR3 : (FR3.drop 46).take 1 = [.ite (.zero .a0) RK fail0] := rfl
theorem hFKy : (FK.drop 28).take 1 = [.ite (.zero .a0) elemOrder (.block [])] := rfl
theorem hFK : (FK.drop 29).take 1 = [.ite (.zero .a0) Verify.body fail0] := rfl

theorem runT : ∀ v s, C0 v s → WP isa (Code.seqL FT) s fun _ => True := fun _ s h =>
  let ⟨tr, t, e, _⟩ := verify_correct s h.1
  ⟨tr, t, exec_flat.mp e, trivial⟩

theorem runX1 : ∀ v s, ΦX1 v s → WP isa (Code.seqL FX1) s fun _ => True := run_then runT hFT
theorem runX2 : ∀ v s, ΦX2 v s → WP isa (Code.seqL FX2) s fun _ => True := run_then runX1 hFX1
theorem runR0 : ∀ v s, ΦR0 v s → WP isa (Code.seqL FR0) s fun _ => True := run_then runX2 hFX2
theorem runR1 : ∀ v s, ΦR1 v s → WP isa (Code.seqL FR1) s fun _ => True := run_then runR0 hFR0
theorem runR2 : ∀ v s, ΦR2 v s → WP isa (Code.seqL FR2) s fun _ => True := run_then runR1 hFR1
theorem runR3 : ∀ v s, ΦR3 v s → WP isa (Code.seqL FR3) s fun _ => True := run_then runR2 hFR2
theorem runEg : ∀ v s, ΦEg v s → WP isa (Code.seqL FE) s fun _ => True := run_then runR3 hFR3g
theorem runK : ∀ v s, ΦK v s → WP isa (Code.seqL FK) s fun _ => True := run_then runR3 hFR3
theorem runEy : ∀ v s, ΦEy v s → WP isa (Code.seqL FE) s fun _ => True := run_then runK hFKy
theorem runB : ∀ v s, ΦB v s → WP isa (Code.seqL FB) s fun _ => True := run_then runK hFK

end VG.Proof.Dsa.RISCV64.CT

module

import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Frame
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyLayout
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Bignum.PackedRead
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Framework.RISCV64.Loops

/-! # DSA parameter search on RISC-V: pieces, states of the search, header words and copies

Pieces proven correct and constant time at once (`VP`), the states of the
search with their data (`SS`, `St`), loads and stores of the header's words,
and the copies within `scratch`, each in its section below.

`scrB_ok`: `scrB rd o` puts the address of byte `o` of `scratch` in `rd`, for
`o` a multiple of 4096 below 32 KiB. `copyN_vp`: a copy (`copyN`) whose
prologue puts public addresses `S` and `D` and the count in `a0`–`a2`
(`ProOk`), into a range of `scratch` past the header and apart from the key
working space: the claims apart from the destination kept, the destination's
bytes those of the source. The prologues of the search's copies:
`pro_scr_scr`, `pro_ld_scr`, `pro_scr_big`.
-/

@[expose] public section

/-! ## DSA parameter search on RISC-V: pieces proven correct and constant time at once

As on PPC64LE (`Proof/Dsa/PPC64LE/Gen/VP.lean`): `VP F c G`: from any state at the
stage `F σ` of a run from `σ`, `c` ends at the stage `G σ` (`wp`), and two
runs, each at the stage `F` of its own run, leak the same trace and end at
the stages `G` (`ct`). The stages carry the public parameters both runs
share, so that a piece checked by the taint analysis needs only that the
registers it takes as public are determined by them (`VP.taint`), and pieces
compose by `seq`, `ite` and `loop` (whose number of iterations is public).
-/

namespace VG.Proof.Dsa.RISCV64.PSearch
open VG VG.RISCV64

/-- Two runs, each at the stage `F` of its own run from `σ`. -/
def Two (F : State → State → Prop) (s₁ s₂ : State) : Prop := ∃ σ₁ σ₂, F σ₁ s₁ ∧ F σ₂ s₂

/-- The stage `F` of a run from `σ`, whose states name the statics `σ` names. -/
def Sy (F : State → State → Prop) (σ s : State) : Prop := F σ s ∧ s.syms = σ.syms

structure VP (F : State → State → Prop) (c : Prog isa) (G : State → State → Prop) : Prop where
  wp : ∀ σ s, F σ s → s.syms = σ.syms → WP isa c s (G σ)
  ct : RelCT isa (Two (Sy F)) c (Two (Sy G))

namespace VP

variable {F G H : State → State → Prop}

/-- The stage after a piece names the statics of the run's start. -/
theorem wps {c : Prog isa} (wp : ∀ σ s, F σ s → s.syms = σ.syms → WP isa c s (G σ)) {σ s : State}
    (hs : F σ s) (hy : s.syms = σ.syms) : WP isa c s (Sy G σ) :=
  WP.mono_syms (wp σ s hs hy) fun _ ht ty => ⟨ht, ty.trans hy⟩

/-- From a relation of any two runs and correctness of each. -/
theorem of_ct' {c : Prog isa}
    (ct : ∀ σ₁ σ₂, RelCT isa (fun s₁ s₂ => Sy F σ₁ s₁ ∧ Sy F σ₂ s₂) c (fun _ _ => True))
    (wp : ∀ σ s, F σ s → s.syms = σ.syms → WP isa c s (G σ)) : VP F c G := by
  refine ⟨wp, ?_⟩
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨σ₁, σ₂, h₁, h₂⟩ e₁ e₂
  have r := ((ct σ₁ σ₂).wp (F₁ := Sy G σ₁) (F₂ := Sy G σ₂) fun s t h =>
    ⟨wps wp h.1.1 h.1.2, wps wp h.2.1 h.2.2⟩) s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂⟩ e₁ e₂
  exact ⟨r.1, σ₁, σ₂, r.2.2.1, r.2.2.2⟩

/-- From a relation of any two runs and correctness of each. -/
theorem of_ct {c : Prog isa}
    (ct : ∀ σ₁ σ₂, RelCT isa (fun s₁ s₂ => F σ₁ s₁ ∧ F σ₂ s₂) c (fun _ _ => True))
    (wp : ∀ σ s, F σ s → WP isa c s (G σ)) : VP F c G :=
  of_ct' (fun σ₁ σ₂ => (ct σ₁ σ₂).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h)
    fun σ s hs _ => wp σ s hs

/-- A piece the taint analysis checks with the registers `rs` public. -/
theorem taint {c : Prog isa} (rs : List Reg)
    (cert : ∃ hc, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs rs) c hc).isSome = true)
    (sp : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → s₁.sp = s₂.sp)
    (regs : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (wp : ∀ σ s, F σ s → WP isa c s (G σ)) : VP F c G := by
  obtain ⟨_, hc⟩ := cert
  exact of_ct (fun σ₁ σ₂ => RelCT.taint (A := VG.RISCV64.taint) (Taint.ofRegs rs)
    (fun s t h => ⟨sp _ _ _ _ h.1 h.2, fun r hr => regs _ _ _ _ h.1 h.2 r
      (by simpa [Taint.ofRegs] using RegSet.mem_ofList.mp hr)⟩) hc) wp

theorem mono {F' G' : State → State → Prop} {c : Prog isa} (h : VP F c G)
    (hF : ∀ σ s, F' σ s → F σ s) (hG : ∀ σ s, G σ s → G' σ s) : VP F' c G' :=
  ⟨fun σ s hs hy => WP.mono (h.wp σ s (hF σ s hs) hy) (hG σ),
    h.ct.mono (fun _ _ ⟨σ₁, σ₂, h₁, h₂⟩ => ⟨σ₁, σ₂, ⟨hF _ _ h₁.1, h₁.2⟩, ⟨hF _ _ h₂.1, h₂.2⟩⟩)
      fun _ _ ⟨σ₁, σ₂, h₁, h₂⟩ => ⟨σ₁, σ₂, ⟨hG _ _ h₁.1, h₁.2⟩, ⟨hG _ _ h₂.1, h₂.2⟩⟩⟩

theorem seq {c₁ c₂ : Prog isa} (h₁ : VP F c₁ G) (h₂ : VP G c₂ H) : VP F (.seq c₁ c₂) H :=
  ⟨fun σ _ hs hy => WP.seq (WP.mono (wps h₁.wp hs hy) fun t ht => h₂.wp σ t ht.1 ht.2), RelCT.seq h₁.ct h₂.ct⟩

theorem assoc {a b c : Prog isa} (h : VP F (.seq (.seq a b) c) G) : VP F (.seq a (.seq b c)) G :=
  ⟨fun σ s hs hy => WP.assoc (h.wp σ s hs hy), RelCT.assoc h.ct⟩

theorem block_append {l₁ l₂ : List Instr} (h₁ : VP F (.block l₁) G) (h₂ : VP G (.block l₂) H) :
    VP F (.block (l₁ ++ l₂)) H :=
  ⟨fun σ _ hs hy => WP.block_append (WP.mono (wps h₁.wp hs hy) fun t ht => h₂.wp σ t ht.1 ht.2),
    RelCT.block_append (RelCT.seq h₁.ct h₂.ct)⟩

theorem block_nil (h : ∀ σ s, F σ s → G σ s) : VP F (.block []) G :=
  ⟨fun σ s hs _ => WP.block_nil (h σ s hs),
    RelCT.block_nil fun _ _ ⟨σ₁, σ₂, h₁, h₂⟩ => ⟨σ₁, σ₂, ⟨h _ _ h₁.1, h₁.2⟩, ⟨h _ _ h₂.1, h₂.2⟩⟩⟩

/-- A branch on a condition both runs agree on. -/
theorem ite {c : Cond} {t e : Prog isa}
    (hc : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → isa.eval c s₁ = isa.eval c s₂)
    (ht : VP (fun σ s => F σ s ∧ isa.eval c s = some true) t G)
    (he : VP (fun σ s => F σ s ∧ isa.eval c s = some false) e G) : VP F (.ite c t e) G := by
  refine ⟨fun σ s hs hy => ?_, ?_⟩
  · obtain ⟨b, hb⟩ : ∃ b, isa.eval c s = some b := by cases c <;> exact ⟨_, rfl⟩
    exact WP.ite b hb (fun h => ht.wp σ s ⟨hs, by rw [hb, h]⟩ hy) (fun h => he.wp σ s ⟨hs, by rw [hb, h]⟩ hy)
  · refine RelCT.ite (fun s₁ s₂ ⟨σ₁, σ₂, h₁, h₂⟩ => hc _ _ _ _ h₁.1 h₂.1) ?_ ?_
    · exact ht.ct.mono (fun s₁ s₂ ⟨⟨σ₁, σ₂, h₁, h₂⟩, e⟩ =>
        ⟨σ₁, σ₂, ⟨⟨h₁.1, e⟩, h₁.2⟩, ⟨h₂.1, (hc _ _ _ _ h₁.1 h₂.1).symm.trans e⟩, h₂.2⟩) fun _ _ h => h
    · exact he.ct.mono (fun s₁ s₂ ⟨⟨σ₁, σ₂, h₁, h₂⟩, e⟩ =>
        ⟨σ₁, σ₂, ⟨⟨h₁.1, e⟩, h₁.2⟩, ⟨h₂.1, (hc _ _ _ _ h₁.1 h₂.1).symm.trans e⟩, h₂.2⟩) fun _ _ h => h

/-- A loop whose iterations left, `n + 1` at the stage `I (n + 1)`, both
runs share: each iteration goes on iff `n > 0`. -/
theorem loop {I : Nat → State → State → Prop} {body : Prog isa} {c : Cond} {Q : State → State → Prop}
    (hb : ∀ n, VP (I (n + 1)) body fun σ s =>
      isa.eval c s = some (decide (0 < n)) ∧ (n = 0 → Q σ s) ∧ (0 < n → I n σ s))
    (n : Nat) : VP (I (n + 1)) (.loop body c) Q := by
  refine ⟨fun σ s hs hy => ?_, ?_⟩
  · refine WP.loop (M := isa) (Q := Q σ) (fun m u => Sy (I (m + 1)) σ u) (fun m u hu => ?_) n s ⟨hs, hy⟩
    refine WP.mono (wps (hb m).wp hu.1 hu.2) fun u' ⟨⟨he, hq, hi⟩, uy⟩ => ?_
    rcases Nat.eq_zero_or_pos m with h0 | hp
    · exact .inl ⟨by rw [he, h0]; rfl, hq h0⟩
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact .inr ⟨by rw [he]; simp, k, by omega, hi hp, uy⟩
  · refine RelCT.loop (M := isa) (fun m => Two (Sy (I (m + 1)))) (fun m => ?_) n
    refine (hb m).ct.mono (fun _ _ h => h) fun s₁ s₂ ⟨σ₁, σ₂, ⟨⟨e₁, q₁, i₁⟩, y₁⟩, ⟨⟨e₂, q₂, i₂⟩, y₂⟩⟩ =>
      ⟨e₁.trans e₂.symm, fun hf => ?_, fun ht => ?_⟩
    · have h0 : m = 0 := by rw [e₁] at hf; simpa using hf
      exact ⟨σ₁, σ₂, ⟨q₁ h0, y₁⟩, ⟨q₂ h0, y₂⟩⟩
    · have hp : 0 < m := by rw [e₁] at ht; simpa using ht
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      exact ⟨k, by omega, σ₁, σ₂, ⟨i₁ hp, y₁⟩, ⟨i₂ hp, y₂⟩⟩

/-- A piece no state reaches. -/
theorem of_false {c : Prog isa} (h : ∀ σ s, ¬ F σ s) : VP F c G :=
  ⟨fun σ s hs => absurd hs (h σ s), fun _ _ _ _ _ _ ⟨σ, _, h₁, _⟩ => absurd h₁.1 (h σ _)⟩

/-- A stage's pure facts, as hypotheses. -/
theorem intro {P : Prop} {F Q : State → State → Prop} {c : Prog isa} (h : P → VP F c Q) :
    VP (fun σ s => P ∧ F σ s) c Q := by
  by_cases hp : P
  · exact (h hp).mono (fun σ s h => h.2) fun _ _ h => h
  · exact VP.of_false fun σ s h => hp h.1

end VP

end VG.Proof.Dsa.RISCV64.PSearch

/-! ## DSA parameter search on RISC-V: a state of the search with its data

As on PPC64LE (`Proof/Dsa/PPC64LE/Gen/St.lean`), in words of 64 bits.
`SS G STK σ c s`: a state of the search (`GI`), with the bytes the claims
`c.cl` of `scratch` hold (past the header, apart from the key working
space), and the arrays and slots of the key working space (at `kB p_len`)
that `c` lists. The key working space's registers are not kept: the power,
in the P space, uses them; each phase of arithmetic sets them (`ksRegs`).
-/

namespace VG.Proof.Dsa.RISCV64.PSearch
open VG VG.RISCV64 VG.RISCV64.Steps
open VG.Impl.Dsa.RISCV64.ParameterSearch
open VG.Proof.Rsa.RISCV64.Keys (arr num slot S arr_end)

/-- Claims on `scratch`: the bytes at an offset. -/
abbrev Claims := List (Nat × List Byte)

/-- The key working space's bytes. -/
def kz (pLen : Nat) : Nat := Impl.Rsa.RISCV64.Keys.hdr + nArrs * S (pLen / 8)

namespace GP
variable (G : GP)

/-- The key working space. -/
abbrev KB : Addr := G.sa (kB G.pLen)
abbrev w : Nat := G.pLen / 8
abbrev rK : Region := ⟨G.KB, kz G.pLen⟩

end GP

/-- The claims hold. -/
def SB (G : GP) (m : Mem) (cl : Claims) : Prop :=
  ∀ x ∈ cl, Spec.Rsa.bytesAt m (G.sa x.1) x.2.length = x.2

/-- What a stage keeps: header words, claims, arrays and key slots. -/
structure Cfg where
  V : Nat → BitVec 64 := fun _ => 0
  LS : List Nat := []
  cl : Claims := []
  A : Nat → Nat := fun _ => 0
  live : List Nat := []
  KV : Nat → Nat := fun _ => 0
  kls : List Nat := []

/-- A key slot a stage keeps. -/
abbrev KlsOk (d : Nat) : Prop := d + 8 ≤ Impl.Rsa.RISCV64.Keys.hdr ∧ d % 8 = 0

/-- A claim's place: past the header, apart from the key working space,
within `scratch`. -/
abbrev ClOk (G : GP) (x : Nat × List Byte) : Prop :=
  hEnd ≤ x.1 ∧ (x.1 + x.2.length ≤ kB G.pLen ∨ wB G.pLen ≤ x.1) ∧ x.1 + x.2.length ≤ G.scrLen * 8

structure SS (G : GP) (STK : Nat) (σ : State) (c : Cfg) (s : State) : Prop where
  gi : GI G STK σ c.V c.LS s
  sb : SB G s.mem c.cl
  clOk : ∀ x ∈ c.cl, ClOk G x
  arrs : ∀ j ∈ c.live, num s.mem G.KB G.w j = c.A j
  liveOk : ∀ j ∈ c.live, j < nArrs
  ksl : ∀ d ∈ c.kls, slot s.mem G.KB d = c.KV d
  kslOk : ∀ d ∈ c.kls, KlsOk d

/-! ## Sizes -/

section
variable {G : GP} {STK : Nat} {σ : State} {V : Nat → BitVec 64} {LS : List Nat} {s : State}

/-- The search's layout for each width: the P space, the key working space
and the working space of the functions we call in turn within `scratch`. -/
theorem lay_ok {L : Nat} (hL : L = 128 ∨ L = 256 ∨ L = 384) :
    pB + pBytes L ≤ kB L ∧ kB L + kz L ≤ wB L ∧ wB L + 256 * L ≤ 8 * (64 * L + 1024) ∧
      wB L % 4096 = 0 ∧ kB L % 4096 = 0 ∧ wB L < 2 ^ 31 := by
  rcases hL with rfl | rfl | rfl <;> decide

theorem GI.wBig (h : GI G STK σ V LS s) : wB G.pLen + 256 * G.pLen ≤ G.scrLen * 8 := by
  have := h.scrBig; have := (lay_ok h.lens).2.2.1; omega

theorem GI.kBig (h : GI G STK σ V LS s) : kB G.pLen + kz G.pLen ≤ wB G.pLen := (lay_ok h.lens).2.1

theorem GI.kSub (h : GI G STK σ V LS s) : Region.Sub G.rK G.rScr :=
  sw G (by have := h.wBig; have := h.kBig; omega)

/-- The key working space is apart from the ranges of `scratch` apart from it. -/
theorem GI.kdisj (h : GI G STK σ V LS s) {o n : Nat} (ho : o + n ≤ kB G.pLen ∨ wB G.pLen ≤ o)
    (hon : o + n ≤ G.scrLen * 8) : G.rK.Disjoint (G.rs o n) := by
  have := h.wBig; have := h.kBig
  exact h.sdisj (by omega) (by omega) hon

end

/-! ## Claims -/

theorem SB.frame {G : GP} {m m' : Mem} {cl : Claims} {rs : List Region} (h : SB G m cl) (f : Frame rs m m')
    (hd : ∀ x ∈ cl, ∀ r ∈ rs, (G.rs x.1 x.2.length).Disjoint r) (hl : ∀ x ∈ cl, x.2.length ≤ 2 ^ 64) :
    SB G m' cl := fun x hx => by
  rw [VG.Proof.Dsa.Generation.frame_bytesAt f (hd x hx) (hl x hx)]; exact h x hx

theorem SB.sub {G : GP} {m : Mem} {cl cl' : Claims} (h : SB G m cl) (hs : ∀ x ∈ cl', x ∈ cl) : SB G m cl' :=
  fun x hx => h x (hs x hx)

theorem SB.cons {G : GP} {m : Mem} {cl : Claims} (h : SB G m cl) {o : Nat} {bs : List Byte}
    (e : Spec.Rsa.bytesAt m (G.sa o) bs.length = bs) : SB G m ((o, bs) :: cl) := fun x hx => by
  rcases List.mem_cons.mp hx with rfl | hx
  · exact e
  · exact h x hx

/-- A claim apart from the range `[o, o + n)`. -/
abbrev Apart (o n : Nat) (x : Nat × List Byte) : Prop := x.1 + x.2.length ≤ o ∨ o + n ≤ x.1

/-! ## The key working space through other steps -/

theorem kz_le {L : Nat} (hL : L = 128 ∨ L = 256 ∨ L = 384) : kz L < 2 ^ 63 := by
  rcases hL with rfl | rfl | rfl <;> decide

/-- The arrays fit the key working space. -/
theorem arrs_fit {L j : Nat} (hj : j < nArrs) :
    arr (L / 8) j + S (L / 8) ≤ kz L := by
  have := arr_end (w := L / 8) hj
  simp only [kz, S, nArrs, arr] at *
  omega

/-- Words read past a `Frame` that leaves their region alone. -/
theorem wordsVal_frame {m m' : Mem} {base : Addr} {d n : Nat} {rs : List Region} {r : Region}
    (F : Frame rs m m') (inside : r.Contains (VG.Proof.Mont.off base d) (8 * n))
    (apart : ∀ other ∈ rs, r.Disjoint other) (fit : 8 * n < 2 ^ 64) :
    VG.Proof.Mont.wordsVal m' base d n = VG.Proof.Mont.wordsVal m base d n := by
  rw [VG.Proof.Bignum.wordsVal_read, VG.Proof.Bignum.wordsVal_read, F.read inside apart fit]

theorem num_frame {B : Addr} {L : Nat} (hL : L = 128 ∨ L = 256 ∨ L = 384) {m m' : Mem}
    {rs : List Region} (f : Frame rs m m') (hd : ∀ r ∈ rs, (⟨B, kz L⟩ : Region).Disjoint r)
    {j : Nat} (hj : j < nArrs) : num m' B (L / 8) j = num m B (L / 8) j := by
  have := arrs_fit (L := L) hj
  have := kz_le hL
  refine wordsVal_frame f (Offset.contains_base _ (by simp only [S] at *; omega) (by omega)) hd
    (by omega)

theorem slot_frame {B : Addr} {L : Nat} {m m' : Mem}
    {rs : List Region} (f : Frame rs m m') (hd : ∀ r ∈ rs, (⟨B, kz L⟩ : Region).Disjoint r)
    {d : Nat} (hdk : KlsOk d) : slot m' B d = slot m B d := by
  obtain ⟨h1, _⟩ := hdk
  simp only [slot, VG.Proof.Mont.word, VG.Proof.Mont.off]
  rw [f.readW (r := ⟨B, kz L⟩) (Offset.contains_base _ (by simp only [kz] at *; omega) (by simp only [kz, Impl.Rsa.RISCV64.Keys.hdr] at *; omega)) hd (by decide)]

/-! ## Steps that keep a state of the search -/

section
variable {G : GP} {STK : Nat} {σ : State} {c : Cfg} {s t : State}

theorem SS.lens (h : SS G STK σ c s) : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384 := h.gi.lens

/-- Registers other than `s6` alone change. -/
theorem SS.of_keep {ws : List Reg} (h : SS G STK σ c s) (r : Keep ws s t) (m : t.mem = s.mem)
    (sp : t.sp = s.sp) (h6 : .s6 ∉ ws := by decide) : SS G STK σ c t :=
  ⟨h.gi.of_keep r m sp h6, m ▸ h.sb, h.clOk, m ▸ h.arrs, h.liveOk, m ▸ h.ksl, h.kslOk⟩

theorem SS.of_upd {r : Reg} {v : BitVec 64} (h : SS G STK σ c s) (u : Upd s t r v) (h6 : r ≠ .s6) :
    SS G STK σ c t :=
  h.of_keep (ws := [r]) ⟨fun r' hr' => u.other r' (by simpa using hr'), u.rd, u.wr⟩ u.mem u.sp
    (by simpa using h6.symm)

/-- Fewer header words, claims, arrays or key slots. -/
theorem SS.mono (h : SS G STK σ c s) {c' : Cfg} (hV : ∀ o ∈ c'.LS, o ∈ c.LS ∧ c.V o = c'.V o)
    (hcl : ∀ x ∈ c'.cl, x ∈ c.cl) (hA : ∀ j ∈ c'.live, j ∈ c.live ∧ c.A j = c'.A j)
    (hK : ∀ d ∈ c'.kls, d ∈ c.kls ∧ c.KV d = c'.KV d) : SS G STK σ c' s := by
  obtain ⟨gi, sb, clOk, arrs, liveOk, ksl, kslOk⟩ := h
  refine ⟨⟨gi.pre, gi.hG, gi.sp, gi.rd, gi.wr, gi.s6, gi.saved, gi.ra, gi.fixed, fun o ho => ?_,
    fun o ho => gi.ls o (hV o ho).1, gi.frame⟩, sb.sub hcl, fun x hx => clOk x (hcl x hx), fun j hj => ?_,
    fun j hj => liveOk j (hA j hj).1, fun d hd => ?_, fun d hd => kslOk d (hK d hd).1⟩
  · rw [← (hV o ho).2]; exact gi.slots o (hV o ho).1
  · rw [← (hA j hj).2]; exact arrs j (hA j hj).1
  · rw [← (hK d hd).2]; exact ksl d (hK d hd).1

/-- The ranges `(o, n)` of `scratch`. -/
abbrev GP.rss (G : GP) (os : List (Nat × Nat)) : List Region := os.map fun p => G.rs p.1 p.2

/-- A step that writes the ranges `os` of `scratch`, past the header and
apart from the key working space, and the stack below the stack pointer: the
claims `cl'`, each kept and apart from the ranges, or holding. -/
theorem SS.of_scrs {ws : List Reg} (h : SS G STK σ c s) (r : Keep ws s t) (sp : t.sp = s.sp)
    {os : List (Nat × Nat)} (hon : ∀ p ∈ os, ClOk G (p.1, List.replicate p.2 0))
    (f : Frame (G.rss os ++ [rBelow σ STK]) s.mem t.mem) {cl' : Claims}
    (hcl : ∀ x ∈ cl', (x ∈ c.cl ∧ ∀ p ∈ os, Apart p.1 p.2 x) ∨
      (Spec.Rsa.bytesAt t.mem (G.sa x.1) x.2.length = x.2 ∧ ClOk G x))
    (h6 : .s6 ∉ ws := by decide) : SS G STK σ { c with cl := cl' } t := by
  have gi := h.gi
  have big := gi.wBig
  have kb := gi.kBig
  have fit := gi.scrFit
  have hE := gi.hEnd_le
  have hon' : ∀ p ∈ os, hEnd ≤ p.1 ∧ (p.1 + p.2 ≤ kB G.pLen ∨ wB G.pLen ≤ p.1) ∧ p.1 + p.2 ≤ G.scrLen * 8 :=
    fun p hp => by have := hon p hp; simp only [ClOk, List.length_replicate] at this; exact this
  have mem : ∀ r' ∈ G.rss os ++ [rBelow σ STK], (∃ p ∈ os, r' = G.rs p.1 p.2) ∨ r' = rBelow σ STK :=
    fun r' hr' => by
      simp only [GP.rss, List.mem_append, List.mem_map, List.mem_singleton] at hr'
      rcases hr' with ⟨p, hp, rfl⟩ | rfl
      · exact .inl ⟨p, hp, rfl⟩
      · exact .inr rfl
  have kd : ∀ r' ∈ G.rss os ++ [rBelow σ STK], (⟨G.KB, kz G.pLen⟩ : Region).Disjoint r' := fun r' hr' => by
    rcases mem r' hr' with ⟨p, hp, rfl⟩ | rfl
    · obtain ⟨_, a, b⟩ := hon' p hp; exact gi.kdisj a b
    · exact gi.scr_below (by omega)
  have gi' : GI G STK σ c.V c.LS t := by
    have hd : ∀ q, q + 8 ≤ hEnd → ∀ r' ∈ G.rss os ++ [rBelow σ STK], (G.rs q 8).Disjoint r' := fun q hq r' hr' => by
      rcases mem r' hr' with ⟨p, hp, rfl⟩ | rfl
      · obtain ⟨a, _, b⟩ := hon' p hp; exact gi.sdisj (.inl (by omega)) (by omega) b
      · exact gi.scr_below (by omega)
    refine ⟨gi.pre, gi.hG, sp.trans gi.sp, r.2.1.trans gi.rd, r.2.2.trans gi.wr, (r.gpr h6).trans gi.s6,
      fun i hi => ?_, ?_, fun p hp => ?_, fun p hp => ?_, gi.ls, gi.frame.trans (f.sub fun x hx => ?_)⟩
    · rw [fw_frame f (hd _ (by simp only [hEnd]; omega))]; exact gi.saved i hi
    · rw [fw_frame f (hd _ (by decide))]; exact gi.ra
    · rw [fw_frame f (hd _ (by have := (fixed_ok G p hp).1; simp only [hEnd]; omega))]; exact gi.fixed p hp
    · rw [fw_frame f (hd _ (by have := (gi.ls p hp).1; simp only [hEnd]; omega))]; exact gi.slots p hp
    · rcases mem x hx with ⟨p, hp, rfl⟩ | rfl
      · exact ⟨G.rScr, List.mem_cons_self, sw G (hon' p hp).2.2⟩
      · exact ⟨rBelow σ STK, by simp, fun _ h => h⟩
  refine ⟨gi', fun x hx => ?_, fun x hx => ?_, fun j hj => ?_, h.liveOk, fun d hd => ?_, h.kslOk⟩
  · rcases hcl x hx with ⟨hm, ha⟩ | ⟨e, _⟩
    · obtain ⟨_, _, xb⟩ := h.clOk x hm
      rw [VG.Proof.Dsa.Generation.frame_bytesAt f (fun r' hr' => by
        rcases mem r' hr' with ⟨p, hp, rfl⟩ | rfl
        · exact gi.sdisj (ha p hp) xb (hon' p hp).2.2
        · exact gi.scr_below xb) (by omega)]
      exact h.sb x hm
    · exact e
  · rcases hcl x hx with ⟨hm, _⟩ | ⟨_, b⟩
    · exact h.clOk x hm
    · exact b
  · rw [num_frame h.lens f kd (h.liveOk j hj)]; exact h.arrs j hj
  · rw [slot_frame f kd (h.kslOk d hd)]; exact h.ksl d hd

/-- The registers a call may change. -/
abbrev volatile : List Reg :=
  [.ra, .t0, .t1, .t2, .t3, .t4, .t5, .t6, .a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7]

theorem keep_of_preserved {s t : State} (g : ∀ r ∈ preserved, t.gpr r = s.gpr r) (rd : t.rd = s.rd)
    (wr : t.wr = s.wr) : Keep volatile s t :=
  ⟨fun r hr => g r (by revert hr; cases r <;> decide), rd, wr⟩

/-- `c` with the header word `o` := `v`. -/
abbrev Cfg.setV (c : Cfg) (o : Nat) (v : BitVec 64) : Cfg := { c with V := upd c.V o v, LS := o :: c.LS }

/-- `sd r, o(s6)` of a variable header word keeps the claims, arrays and key
slots. -/
theorem SS.stF (h : SS G STK σ c s) {o : Nat} (hv : VarOk G o) {r : Reg}
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, SS G STK σ (c.setV o (s.gpr r)) t → Mupd s t (s.mem.writeW (G.sa o) (s.gpr r)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (st r o :: rest)) s Q := by
  refine h.gi.stF hv fun t gi m => k t ?_ m
  have gi₀ := h.gi
  have big := gi₀.wBig
  have kb := gi₀.kBig
  have hE := gi₀.hEnd_le
  obtain ⟨oS, _, _, _⟩ := hv
  have f : Frame [G.rs o 8] s.mem t.mem := by
    rw [m.mem]; exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  have hd : (G.rs o 8).Disjoint (⟨G.KB, kz G.pLen⟩ : Region) :=
    (gi₀.kdisj (o := o) (n := 8) (.inl (by simp only [kB, pB, fSave] at oS ⊢; omega))
      (by simp only [hEnd] at hE; omega)).symm
  refine ⟨gi, h.sb.frame f (fun x hx r' hr' => ?_) (fun x hx => ?_), h.clOk, fun j hj => ?_, h.liveOk,
    fun d hd' => ?_, h.kslOk⟩
  · simp only [List.mem_singleton] at hr'; subst hr'
    obtain ⟨a, _, b⟩ := h.clOk x hx
    exact gi₀.sdisj (.inr (by simp only [hEnd] at a; omega)) b (by simp only [hEnd] at hE; omega)
  · have := (h.clOk x hx).2.2; have := gi₀.scrFit; omega
  · rw [num_frame h.lens f (fun r' hr' => by simp only [List.mem_singleton] at hr'; subst hr'; exact hd.symm)
      (h.liveOk j hj)]
    exact h.arrs j hj
  · rw [slot_frame f (fun r' hr' => by simp only [List.mem_singleton] at hr'; subst hr'; exact hd.symm)
      (h.kslOk d hd')]
    exact h.ksl d hd'

end

end VG.Proof.Dsa.RISCV64.PSearch

/-! ## DSA parameter search on RISC-V: header words in pieces

As on PPC64LE (`Proof/Dsa/PPC64LE/Gen/Pieces.lean`). `WP.wr`: an
instruction that writes one register. The taint analysis does not follow the
header's words, which the search keeps its state in: a load of one (`ld`) and
a store into one (`st`) leak only addresses from `s6`, which holds `scratch`
in both runs of the search, so they are analysed with `s6` public (`ld_vp`,
`st_vp`, `stImm_vp`, `cmpF_vp`), and the code between them with the registers
the loads set public (`VP.taint`).
-/

namespace VG.Proof.Dsa.RISCV64.PSearch
open VG VG.RISCV64 VG.RISCV64.Steps
open VG.Impl.Dsa.RISCV64.ParameterSearch

/-- An instruction that writes `v` to `d`. -/
theorem WP.wr {i : Instr} {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {v : BitVec 64}
    (h : exec i s = some (s.write d v)) (k : ∀ s', Upd s s' d v → WP isa (.block is) s' Q) :
    WP isa (.block (i :: is)) s Q :=
  WP.cons h (k _ (Upd.write _ _ _))

section
variable {G : GP} {STK : Nat}

/-- The stage's states hold `scratch` in `s6` and have the call's stack pointer. -/
abbrev Pub (G : GP) (F : State → State → Prop) : Prop :=
  ∀ σ s, F σ s → s.gpr .s6 = G.scr ∧ s.sp = G.sp

theorem SS.pub {F : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s) :
    Pub G F := fun σ s h => ⟨(hF σ s h).gi.s6, by rw [(hF σ s h).gi.sp, ← (hF σ s h).gi.hG]; rfl⟩

/-- A piece analysed with `s6` and `rs` public. -/
theorem VP.pub {F Q : State → State → Prop} {c : Prog isa} (hp : Pub G F) (rs : List Reg)
    (cert : ∃ hc, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs (.s6 :: rs)) c hc).isSome = true)
    (regs : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (wp : ∀ σ s, F σ s → WP isa c s (Q σ)) : VP F c Q :=
  VP.taint (.s6 :: rs) cert (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [(hp _ _ h₁).2, (hp _ _ h₂).2])
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [(hp _ _ h₁).1, (hp _ _ h₂).1]
      · exact regs _ _ _ _ h₁ h₂ r hr) wp

end

/-- `ld t, o(s6)` of a header word whose value `v` is known, keeping a stage. -/
theorem SS.ldK {G : GP} {STK : Nat} {σ s : State} {c : Cfg} (h : SS G STK σ c s) {o : Nat} (ho : o + 8 ≤ hEnd)
    (h8 : o % 8 = 0) {v : BitVec 64} (hv : fw s.mem G o = v) {t : Reg} (ht : t ≠ .s6) {rest : List Instr}
    {Q : State → Prop} (k : ∀ s', SS G STK σ c s' → Upd s s' t v → WP isa (.block rest) s' Q) :
    WP isa (.block (ld t o :: rest)) s Q :=
  h.gi.ldV ho h8 hv fun s' u => k s' (h.of_upd u ht) u

/-! ## Header words as pieces -/

section
variable {G : GP} {STK : Nat}

/-- A load of a header word whose value both runs know. -/
theorem ld_vp {P Q : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, P σ s → SS G STK σ (c σ) s)
    {r : Reg} (hr : r ≠ .s6) {o : Nat} (ho : o + 8 ≤ hEnd) (h8 : o % 8 = 0) {x : BitVec 64}
    (hx : ∀ σ s, P σ s → fw s.mem G o = x)
    (k : ∀ σ s t, P σ s → SS G STK σ (c σ) t → Upd s t r x → Q σ t) : VP P (.block [ld r o]) Q := by
  refine VP.pub (SS.pub hF) [] ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6]) (.block [ld r o]),
    by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  exact (hF σ s hs).ldK ho h8 (hx σ s hs) hr fun t h u => WP.block_nil (k σ s t hs h u)

/-- A store into a variable word of the header. -/
theorem st_vp {P Q : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, P σ s → SS G STK σ (c σ) s)
    {r : Reg} {o : Nat} (hv : VarOk G o)
    (k : ∀ σ s t, P σ s → SS G STK σ ((c σ).setV o (s.gpr r)) t → Keep [] s t → Q σ t) :
    VP P (.block [st r o]) Q := by
  refine VP.pub (SS.pub hF) [] ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6]) (.block [st r o]),
    by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  exact (hF σ s hs).stF hv fun t h m => WP.block_nil (k σ s t hs h ⟨fun r _ => by rw [m.gpr], m.rd, m.wr⟩)

/-- `stImm o v`: the header word `o` := `v`. -/
theorem stImm_vp {P Q : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, P σ s → SS G STK σ (c σ) s)
    {o v : Nat} (hv : v < 2048) (ho : VarOk G o)
    (k : ∀ σ s t, P σ s → SS G STK σ ((c σ).setV o (BitVec.ofNat 64 v)) t → Keep [.t2] s t → Q σ t) :
    VP P (.block (stImm o v)) Q := by
  refine VP.pub (SS.pub hF) [] ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6]) (.block (stImm o v)),
    by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  refine wp_li hv fun s₁ u₁ => ?_
  have h₁ : SS G STK σ (c σ) s₁ := (hF σ s hs).of_upd u₁ (by decide)
  refine h₁.stF ho fun t h m => WP.block_nil (k σ s t hs (by rw [u₁.gpr] at h; exact h) ?_)
  exact ⟨fun r hr => by rw [m.gpr, u₁.other _ (by simpa using hr)], by rw [m.rd, u₁.rd], by rw [m.wr, u₁.wr]⟩

theorem sub_beq_zero (x y : BitVec 64) : (x - y == 0) = (x == y) := by
  by_cases h : x = y
  · subst h; simp
  · have : x - y ≠ 0 := fun e => h (by rw [← BitVec.sub_add_cancel x y, e]; exact BitVec.zero_add y)
    rw [beq_false_of_ne this, beq_false_of_ne h]

/-- `cmpF o v`: `t2 = 0` iff the header word `o`, which both runs know, is `v`. -/
theorem cmpF_vp {P Q : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, P σ s → SS G STK σ (c σ) s)
    {o v : Nat} (ho : o + 8 ≤ hEnd) (h8 : o % 8 = 0) (hv : v ≤ 2048) {x : BitVec 64}
    (hx : ∀ σ s, P σ s → fw s.mem G o = x)
    (k : ∀ σ s t, P σ s → SS G STK σ (c σ) t → Keep [.t2] s t →
      isa.eval (.zero .t2) t = some (x == BitVec.ofNat 64 v) → Q σ t) : VP P (.block (cmpF o v)) Q := by
  refine VP.pub (SS.pub hF) [] ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6]) (.block (cmpF o v)),
    by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  have h := hF σ s hs
  refine h.ldK ho h8 (hx σ s hs) (t := .t2) (by decide) fun s₁ h₁ u₁ => ?_
  refine wp_subi hv fun t u => WP.block_nil ?_
  refine k σ s t hs (h₁.of_upd u (by decide)) ?_ ?_
  · exact ⟨fun r hr => by
      have hr' : r ≠ .t2 := by simpa using hr
      rw [u.other _ hr', u₁.other _ hr'], by rw [u.rd, u₁.rd], by rw [u.wr, u₁.wr]⟩
  · rw [eval_zero, u.gpr, u₁.gpr, sub_beq_zero]

end

end VG.Proof.Dsa.RISCV64.PSearch

namespace VG.Proof.Dsa.RISCV64.PSearch
open VG VG.RISCV64 VG.RISCV64.Steps
open VG.Impl.Dsa.RISCV64.ParameterSearch

/-- The stack the functions the search calls use below the stack pointer. -/
abbrev STK0 : Nat := 512

/-- A stage of the search: a state of the search with the claims, arrays
and slots `c`, from a call with the property `X`. -/
abbrev St (G : GP) (c : Cfg) (X : State → Prop) (σ s : State) : Prop := SS G STK0 σ c s ∧ X σ

theorem GP.sa_add (G : GP) (o i : Nat) : G.sa o + BitVec.ofNat 64 i = G.sa (o + i) := by
  simp only [GP.sa, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- `lui`'s value for the multiples of 4096 below 32 KiB. -/
theorem luiv : ∀ h < 8, sext32 (BitVec.ofNat 20 h ++ (0 : BitVec 12)) = BitVec.ofNat 64 (4096 * h) := by
  decide

/-- `scrB rd o`: `rd := S + o`. -/
theorem scrB_ok {G : GP} {s : State} {rd : Reg} {o : Nat} (hrd : rd ≠ .s6) (h6 : s.gpr .s6 = G.scr)
    (ho : o % 4096 = 0) (h8 : o / 4096 < 8) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Keep [rd] s t → t.mem = s.mem → t.sp = s.sp → t.gpr rd = G.sa o → WP isa (.block rest) t Q) :
    WP isa (.block (scrB rd o ++ rest)) s Q := by
  simp only [scrB, List.cons_append, List.nil_append]
  refine WP.cons exec_lui ?_
  refine wp_add fun t u => ?_
  refine k t ⟨fun r hr => ?_, by rw [u.rd]; rfl, by rw [u.wr]; rfl⟩ (by rw [u.mem]; rfl) (by rw [u.sp]; rfl) ?_
  · have hr' : r ≠ rd := by simpa using hr
    rw [u.other _ hr', RegUpd.gpr_write_of_ne _ _ hr']
  · rw [u.gpr, RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne _ _ (Ne.symm hrd), h6, luiv _ h8,
      show 4096 * (o / 4096) = o by omega, BitVec.add_comm]

/-- A copy's prologue puts `S`, `D` and `n` in `a0`, `a1` and `a2`, changing
only those registers. -/
abbrev ProOk (F : State → State → Prop) (pro : List Instr) (S D : Addr) (n : Nat) : Prop :=
  ∀ σ s, F σ s → WP isa (.block pro) s fun t => Keep [.a0, .a1, .a2] s t ∧ t.mem = s.mem ∧ t.sp = s.sp ∧
    t.gpr .a0 = S ∧ t.gpr .a1 = D ∧ t.gpr .a2 = BitVec.ofNat 64 n

section
variable {G : GP} {STK : Nat}

/-- A copy of `n` bytes from `S` (readable, apart from the destination) into
the range `[dst, dst + n)` of `scratch`, past the header and apart from the
key working space: the claims apart from the destination kept, the
destination's bytes those at `S`. -/
theorem copyN_vp {F Q : State → State → Prop} {c : State → Cfg} {src dst : List Instr} {S : Addr} {o n : Nat}
    (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s) (hn : 0 < n) (hn64 : n < 2 ^ 63)
    (cert : (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s6]) (.block (src ++ dst ++ ([.li .a2 n] : List Instr)))
      (VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6]) (.block (src ++ dst ++ ([.li .a2 n] : List Instr))))).isSome
      = true)
    (hpro : ProOk F (src ++ dst ++ ([.li .a2 n] : List Instr)) S (G.sa o) n)
    (hdo : ∀ σ s, F σ s → ClOk G (o, List.replicate n 0))
    (hSr : ∀ σ s, F σ s → (∀ i < n, InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 i) 1) ∧
      Mem.Sep (G.sa o) n S n)
    (k : ∀ σ s t, F σ s → SS G STK σ { c σ with cl := (c σ).cl.filter fun x => decide (Apart o n x) } t →
      Keep [.a0, .a1, .a2, .a3] s t →
      Spec.Rsa.bytesAt t.mem (G.sa o) n = Spec.Rsa.bytesAt s.mem S n → Q σ t) :
    VP F (copyN src dst n) Q := by
  let M : State → State → Prop := fun σ t => ∃ s, F σ s ∧ SS G STK σ (c σ) t ∧ Keep [.a0, .a1, .a2] s t ∧
    t.sp = s.sp ∧ t.mem = s.mem ∧ t.gpr .a0 = S ∧ t.gpr .a1 = G.sa o ∧ t.gpr .a2 = BitVec.ofNat 64 n
  refine VP.seq (G := M) (VP.pub (SS.pub hF) [] ⟨_, cert⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp))
    fun σ s hs => WP.mono (hpro σ s hs) fun t ⟨K, m, sp, a0, a1, a2⟩ =>
      ⟨s, hs, (hF σ s hs).of_keep K m sp, K, sp, m, a0, a1, a2⟩) ?_
  refine VP.pub (G := G) (fun σ t ⟨_, _, h, _⟩ => ⟨h.gi.s6, by rw [h.gi.sp, ← h.gi.hG]; rfl⟩) [.a0, .a1, .a2]
    ⟨VG.Taint.hintOfSize VG.RISCV64.taint 64 (Taint.ofRegs [.s6, .a0, .a1, .a2])
      (Impl.Words.RISCV64.copyLoop .a3 .a0 .a1 .a2), by kernel_rfl⟩
    (fun σ₁ σ₂ s₁ s₂ ⟨_, _, _, _, _, _, a0, a1, a2⟩ ⟨_, _, _, _, _, _, b0, b1, b2⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a0, b0]
      · rw [a1, b1]
      · rw [a2, b2]) fun σ t ⟨s, hs, h, K₁, sp₁, m₁, t0, t1, t2⟩ => ?_
  have gi := h.gi
  have fit := gi.scrFit
  obtain ⟨dE, dK, dS⟩ := hdo σ s hs
  simp only [List.length_replicate] at dK dS
  obtain ⟨Sr, sep⟩ := hSr σ s hs
  refine WP.sp_eq (WP.mono (copyLoop_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) t hn
    (by omega) t2 (fun i hi => by rw [t0, K₁.2.1, K₁.2.2]; exact Sr i hi)
    (fun i hi => by rw [t1, GP.sa_add]; exact gi.inScr (o := o + i) (n := 1) (by omega)) (by rw [t0, t1]; exact sep))
    fun u ⟨cp, f, kp⟩ spu => ?_)
  have K : Keep [.a0, .a1, .a2, .a3] s u := by
    refine ⟨fun r hr => ?_, by rw [kp.2.1, K₁.2.1], by rw [kp.2.2, K₁.2.2]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [kp.1 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]), K₁.1 r (by simp [hr.1, hr.2.1, hr.2.2.1])]
  refine k σ s u hs ?_ K ?_
  · refine h.of_scrs (os := [(o, n)]) (ws := [.a0, .a1, .a2, .a3]) ⟨fun r hr => kp.1 r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢
        exact ⟨hr.2.2.2, hr.1, hr.2.1, hr.2.2.1⟩), kp.2.1, kp.2.2⟩ spu (fun p hp => by
        simp only [List.mem_singleton] at hp; subst hp; exact ⟨dE, by simpa using dK, by simpa using dS⟩)
      (by rw [t1] at f; exact f.mono fun r hr => by simp at hr ⊢; exact .inl hr) fun x hx => .inl ?_
    obtain ⟨hm, ha⟩ := List.mem_filter.mp hx
    exact ⟨hm, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; simpa using ha⟩
  · simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    rw [← t1, cp i hi', t0, m₁]

end


/-! ## The prologues of the search's copies -/

section
variable {G : GP} {STK : Nat}

/-- `[scr .a0 x] ++ [scr .a1 y] ++ [.li .a2 n]`. -/
theorem pro_scr_scr {F : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s)
    {x y n : Nat} (hx : x < 2048) (hy : y < 2048) (hn : n < 2048) :
    ProOk F (([scr .a0 x] : List Instr) ++ ([scr .a1 y] : List Instr) ++ ([.li .a2 n] : List Instr)) (G.sa x) (G.sa y) n := by
  intro σ s hs
  have h6 := (hF σ s hs).gi.s6
  simp only [scr, List.cons_append, List.nil_append]
  refine wp_addi hx fun s₁ u₁ => wp_addi hy fun s₂ u₂ => wp_li hn fun t u => WP.block_nil ?_
  refine ⟨⟨fun r hr => ?_, by rw [u.rd, u₂.rd, u₁.rd], by rw [u.wr, u₂.wr, u₁.wr]⟩, by rw [u.mem, u₂.mem, u₁.mem],
    by rw [u.sp, u₂.sp, u₁.sp], ?_, ?_, u.gpr⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u.other _ hr.2.2, u₂.other _ hr.2.1, u₁.other _ hr.1]
  · rw [u.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h6]
  · rw [u.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h6]

/-- `[ld .a0 f] ++ [scr .a1 y] ++ [.li .a2 n]`, the header word `f` holding `P`. -/
theorem pro_ld_scr {F : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s)
    {f y n : Nat} {P : Addr} (hf : f + 8 ≤ hEnd) (hf8 : f % 8 = 0) (hP : ∀ σ s, F σ s → fw s.mem G f = P)
    (hy : y < 2048) (hn : n < 2048) :
    ProOk F (([ld .a0 f] : List Instr) ++ ([scr .a1 y] : List Instr) ++ ([.li .a2 n] : List Instr)) P (G.sa y) n := by
  intro σ s hs
  have h := hF σ s hs
  simp only [scr, List.cons_append, List.nil_append]
  refine h.gi.ldV hf hf8 (hP σ s hs) fun s₁ u₁ => wp_addi hy fun s₂ u₂ => wp_li hn fun t u => WP.block_nil ?_
  refine ⟨⟨fun r hr => ?_, by rw [u.rd, u₂.rd, u₁.rd], by rw [u.wr, u₂.wr, u₁.wr]⟩, by rw [u.mem, u₂.mem, u₁.mem],
    by rw [u.sp, u₂.sp, u₁.sp], ?_, ?_, u.gpr⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u.other _ hr.2.2, u₂.other _ hr.2.1, u₁.other _ hr.1]
  · rw [u.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.gi.s6]

/-- `[scr .a0 x] ++ (scrB .a1 o ++ [.addi .a1 .a1 k]) ++ [.li .a2 n]`. -/
theorem pro_scr_big {F : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s)
    {x o k n : Nat} (hx : x < 2048) (ho : o % 4096 = 0) (h8 : o / 4096 < 8) (hk : k < 2048) (hn : n < 2048) :
    ProOk F (([scr .a0 x] : List Instr) ++ (scrB .a1 o ++ ([.addi .a1 .a1 k] : List Instr)) ++ ([.li .a2 n] : List Instr)) (G.sa x) (G.sa (o + k)) n := by
  intro σ s hs
  have h6 := (hF σ s hs).gi.s6
  simp only [scr, List.cons_append, List.append_assoc, List.nil_append]
  refine wp_addi hx fun s₁ u₁ => ?_
  refine scrB_ok (by decide) (by rw [u₁.other _ (by decide), h6]) ho h8 fun s₂ K₂ m₂ sp₂ a₂ => ?_
  refine wp_addi hk fun s₃ u₃ => wp_li hn fun t u => WP.block_nil ?_
  refine ⟨⟨fun r hr => ?_, by rw [u.rd, u₃.rd, K₂.2.1, u₁.rd], by rw [u.wr, u₃.wr, K₂.2.2, u₁.wr]⟩,
    by rw [u.mem, u₃.mem, m₂, u₁.mem], by rw [u.sp, u₃.sp, sp₂, u₁.sp], ?_, ?_, u.gpr⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u.other _ hr.2.2, u₃.other _ hr.2.1, K₂.gpr (by simpa using hr.2.1), u₁.other _ hr.1]
  · rw [u.other _ (by decide), u₃.other _ (by decide), K₂.gpr (by decide), u₁.gpr, h6]
  · rw [u.other _ (by decide), u₃.gpr, a₂, GP.sa_add]

/-- `scrB .a0 o ++ [ld .a1 f] ++ [.li .a2 n]`, the header word `f` holding `P`. -/
theorem pro_big_ld {F : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s)
    {o f n : Nat} {P : Addr} (ho : o % 4096 = 0) (h8 : o / 4096 < 8) (hf : f + 8 ≤ hEnd) (hf8 : f % 8 = 0)
    (hP : ∀ σ s, F σ s → fw s.mem G f = P) (hn : n < 2048) :
    ProOk F (scrB .a0 o ++ ([ld .a1 f] : List Instr) ++ ([.li .a2 n] : List Instr)) (G.sa o) P n := by
  intro σ s hs
  have h := hF σ s hs
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine scrB_ok (by decide) h.gi.s6 ho h8 fun s₁ K₁ m₁ sp₁ a₁ => ?_
  have h₁ : SS G STK σ (c σ) s₁ := h.of_keep K₁ m₁ sp₁
  refine h₁.gi.ldV (v := P) hf hf8 (by rw [m₁]; exact hP σ s hs) fun s₂ u₂ => wp_li hn fun t u => WP.block_nil ?_
  refine ⟨⟨fun r hr => ?_, by rw [u.rd, u₂.rd, K₁.2.1], by rw [u.wr, u₂.wr, K₁.2.2]⟩, by rw [u.mem, u₂.mem, m₁],
    by rw [u.sp, u₂.sp, sp₁], ?_, ?_, u.gpr⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u.other _ hr.2.2, u₂.other _ hr.2.1, K₁.gpr (by simpa using hr.1)]
  · rw [u.other _ (by decide), u₂.other _ (by decide), a₁]
  · rw [u.other _ (by decide), u₂.gpr]

end


/-- Disjoint regions are separate ranges. -/
theorem sep_of_disjoint {a b : Addr} {n k : Nat} (h : (⟨a, n⟩ : Region).Disjoint ⟨b, k⟩) : Mem.Sep a n b k :=
  fun x hx hy => h x (by show (x - a).toNat + 1 ≤ n; omega) (by show (x - b).toNat + 1 ≤ k; omega)

/-! ## Copies as pieces -/

section
variable {G : GP} {STK : Nat}

/-- A copy between two ranges of `scratch` below 2048, past the header, apart
from the key working space and from each other. -/
theorem copyS_vp {F Q : State → State → Prop} {c : State → Cfg} {dst src n : Nat}
    (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s) (hn : 0 < n) (hn2 : n < 2048) (hd2 : dst < 2048)
    (hs2 : src < 2048) (hdo : ∀ σ s, F σ s → ClOk G (dst, List.replicate n 0))
    (hso : ∀ σ s, F σ s → src + n ≤ G.scrLen * 8)
    (hsep : dst + n ≤ src ∨ src + n ≤ dst)
    (k : ∀ σ s t, F σ s → SS G STK σ { c σ with cl := (c σ).cl.filter fun x => decide (Apart dst n x) } t →
      Keep [.a0, .a1, .a2, .a3] s t →
      Spec.Rsa.bytesAt t.mem (G.sa dst) n = Spec.Rsa.bytesAt s.mem (G.sa src) n → Q σ t) :
    VP F (copyS dst src n) Q :=
  copyN_vp hF hn (by omega) (by kernel_rfl) (pro_scr_scr hF hs2 hd2 hn2) hdo
    (fun σ s hs => by
      have gi := (hF σ s hs).gi
      have := hso σ s hs
      refine ⟨fun i hi => by rw [GP.sa_add]; exact gi.inRdWr (o := src + i) (n := 1) (by omega), ?_⟩
      have := (hdo σ s hs).2.2; simp only [List.length_replicate] at this
      exact Offset.sep _ hsep (by omega) (by omega)) k

/-- A copy of `n` bytes from the pointer `P` in the header word `o` (readable,
apart from `scratch`) to a range of `scratch` below 2048, past the header and
apart from the key working space. -/
theorem copyIn_vp {F Q : State → State → Prop} {c : State → Cfg} {o dst n : Nat} {P : Addr}
    (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s) (hn : 0 < n) (hn2 : n < 2048) (hd2 : dst < 2048)
    (ho : o + 8 ≤ hEnd) (h8 : o % 8 = 0) (hP : ∀ σ s, F σ s → fw s.mem G o = P)
    (hdo : ∀ σ s, F σ s → ClOk G (dst, List.replicate n 0))
    (hPr : ∀ σ s, F σ s → InRegions (s.rd ++ s.wr) P n ∧ (⟨P, n⟩ : Region).Disjoint G.rScr)
    (k : ∀ σ s t, F σ s → SS G STK σ { c σ with cl := (c σ).cl.filter fun x => decide (Apart dst n x) } t →
      Keep [.a0, .a1, .a2, .a3] s t →
      Spec.Rsa.bytesAt t.mem (G.sa dst) n = Spec.Rsa.bytesAt s.mem P n → Q σ t) :
    VP F (copyN [ld .a0 o] [scr .a1 dst] n) Q :=
  copyN_vp hF hn (by omega) (by kernel_rfl) (pro_ld_scr hF ho h8 hP hd2 hn2) hdo
    (fun σ s hs => by
      obtain ⟨⟨r, hr, hc⟩, hd⟩ := hPr σ s hs
      refine ⟨fun i hi => ⟨r, hr, hc.byte (by
        rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hi)⟩, ?_⟩
      have := (hdo σ s hs).2.2; simp only [List.length_replicate] at this
      exact sep_of_disjoint ((hd.sub_right (sw G this)).symm)) k

end

end VG.Proof.Dsa.RISCV64.PSearch

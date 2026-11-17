module

public import VerifiedGarbage.Proof.Framework.PPC64LE.ByteStep
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontSum
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Frame
public import VerifiedGarbage.Proof.Rsa.KeyArrays

/-! ### `Dsa.PPC64LE.Gen.Pieces`, which this module and modules that import it used -/

section

/-! ### `Dsa.PPC64LE.Gen.St`, which this module and modules that import it used -/

section

/-! # DSA parameter generation on PPC64LE: a state of the search with its data

`SS G STK σ c s`: a state of the search (`GI`), with the bytes the claims
`c.cl` of `scratch` hold (past the header, apart from the key working
space), and the arrays and header words of the key working space (at
`kB p_len`) that `c` lists. The key working space's registers are not kept:
the power, in the P space, uses them; each phase of arithmetic sets them
(`ksRegs`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE VG.Proof.Rsa.KeyWorkspace
open VG.Impl.Dsa.PPC64LE.Generation
open VG.Proof.Mont (w32 val32 val32_congr)

/-- Claims on `scratch`: the bytes at an offset. -/
abbrev Claims := List (Nat × List Byte)

/-- The key working space's bytes. -/
def kz (pLen : Nat) : Nat := hdr + nArrs * S (pLen / 4)

namespace GP
variable (G : GP)

/-- The key working space. -/
abbrev KB : Addr := G.sa (kB G.pLen)
abbrev w : Nat := G.pLen / 4
abbrev rK : Region := ⟨G.KB, kz G.pLen⟩

end GP

/-- The claims hold. -/
def SB (G : GP) (m : Mem) (cl : Claims) : Prop :=
  ∀ x ∈ cl, Spec.Rsa.bytesAt m (G.sa x.1) x.2.length = x.2

/-- What a stage keeps: header words, claims, arrays and key header words. -/
structure Cfg where
  V : Nat → BitVec 64 := fun _ => 0
  LS : List Nat := []
  cl : Claims := []
  A : Nat → Nat := fun _ => 0
  live : List Nat := []
  KV : Nat → Nat := fun _ => 0
  kls : List Nat := []

/-- A key header word a stage keeps. -/
abbrev KlsOk (d : Nat) : Prop := d + 4 ≤ hdr ∧ d % 4 = 0

/-- A claim's place: past the header, apart from the key working space,
within `scratch`. -/
abbrev ClOk (G : GP) (x : Nat × List Byte) : Prop :=
  hEnd ≤ x.1 ∧ (x.1 + x.2.length ≤ kB G.pLen ∨ wB G.pLen ≤ x.1) ∧ x.1 + x.2.length ≤ G.scrLen * 8

structure SS (G : GP) (STK : Nat) (σ : State) (c : Cfg) (s : State) : Prop where
  gi : GI G STK σ c.V c.LS s
  sb : SB G s.mem c.cl
  clOk : ∀ x ∈ c.cl, ClOk G x
  arrs : Arrs s.mem G.KB G.w c.A c.live
  liveOk : ∀ j ∈ c.live, j < nArrs
  ksl : ∀ d ∈ c.kls, slot s.mem G.KB d = c.KV d
  kslOk : ∀ d ∈ c.kls, KlsOk d

/-! ## Sizes -/

section
variable {G : GP} {STK : Nat} {σ : State} {V : Nat → BitVec 64} {LS : List Nat} {s : State}

theorem GI.lens3 (h : GI G STK σ V LS s) : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384 := by
  rcases h.lens with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> simp [e]

/-- `scratch` holds the working space of the functions we call and everything
below it. -/
theorem GI.wBig (h : GI G STK σ V LS s) : wB G.pLen + 8 * wWords G.pLen ≤ G.scrLen * 8 := by
  have := h.scrBig
  rcases h.lens3 with e | e | e <;> rw [e] at this ⊢
  · have : wB 128 + 8 * wWords 128 ≤ 8 * (64 * 128 + 1024) := by decide
    omega_arith
  · have : wB 256 + 8 * wWords 256 ≤ 8 * (64 * 256 + 1024) := by decide
    omega_arith
  · have : wB 384 + 8 * wWords 384 ≤ 8 * (64 * 384 + 1024) := by decide
    omega_arith

theorem GI.kBig (h : GI G STK σ V LS s) : kB G.pLen + kz G.pLen ≤ wB G.pLen := by
  rcases h.lens3 with e | e | e <;> rw [e] <;> decide

theorem GI.kSub (h : GI G STK σ V LS s) : Region.Sub G.rK G.rScr :=
  sw G (by have := h.wBig; have := h.kBig; omega_arith)

/-- The key working space is apart from the ranges of `scratch` apart from it. -/
theorem GI.kdisj (h : GI G STK σ V LS s) {o n : Nat} (ho : o + n ≤ kB G.pLen ∨ wB G.pLen ≤ o)
    (hon : o + n ≤ G.scrLen * 8) : G.rK.Disjoint (G.rs o n) := by
  have := h.wBig; have := h.kBig
  exact h.sdisj (by omega_using [ho, this]) (by omega_arith) hon

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

theorem w32_frame {B : Addr} {Z : Nat} {m m' : Mem} {rs : List Region} (f : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨B, Z⟩ : Region).Disjoint r) (hZ : Z ≤ 2 ^ 64) {d : Nat} (h : d + 4 ≤ Z) :
    w32 m' B d = w32 m B d := by
  simp only [w32]
  rw [f.readW (r := ⟨B, Z⟩) (Offset.contains_base _ h (by omega_using [hZ, h])) hd (by decide)]

theorem kz_eq {L : Nat} (hL : L = 128 ∨ L = 256 ∨ L = 384) : kz L ≤ 2 ^ 64 := by
  rcases hL with rfl | rfl | rfl <;> decide

/-- The arrays fit the key working space. -/
theorem arrs_fit {L j : Nat} (hL : L = 128 ∨ L = 256 ∨ L = 384) (hj : j < nArrs) :
    arr (L / 4) j + 4 * (L / 4 + 2) ≤ kz L := by
  have := arr_end (w := L / 4) hj
  simp only [arr, S, hdr, nArrs, kz] at *
  rcases hL with rfl | rfl | rfl <;> omega_using [hj]

theorem num_frame {B : Addr} {L : Nat} (hL : L = 128 ∨ L = 256 ∨ L = 384) {m m' : Mem}
    {rs : List Region} (f : Frame rs m m') (hd : ∀ r ∈ rs, (⟨B, kz L⟩ : Region).Disjoint r)
    {j : Nat} (hj : j < nArrs) : num m' B (L / 4) j = num m B (L / 4) j := by
  have := arrs_fit hL hj
  exact val32_congr fun i hi => w32_frame f hd (kz_eq hL) (by omega_using [this, hi])

theorem slot_frame {B : Addr} {L : Nat} (hL : L = 128 ∨ L = 256 ∨ L = 384) {m m' : Mem}
    {rs : List Region} (f : Frame rs m m') (hd : ∀ r ∈ rs, (⟨B, kz L⟩ : Region).Disjoint r)
    {d : Nat} (hdk : KlsOk d) : slot m' B d = slot m B d :=
  w32_frame f hd (kz_eq hL) (by obtain ⟨h1, _⟩ := hdk; simp only [kz, hdr] at h1 ⊢; omega_using [h1])

/-! ## Steps that keep a state of the search -/

section
variable {G : GP} {STK : Nat} {σ : State} {c : Cfg} {s t : State}

theorem SS.lens (h : SS G STK σ c s) : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384 := h.gi.lens3

/-- Registers other than `r28` alone change. -/
theorem SS.of_keep {ws : List Reg} (h : SS G STK σ c s) (r : Keep ws s t) (m : t.mem = s.mem)
    (sp : t.sp = s.sp) (h28 : .r28 ∉ ws := by decide) : SS G STK σ c t :=
  ⟨h.gi.of_keep r m sp h28, m ▸ h.sb, h.clOk, m ▸ h.arrs, h.liveOk, m ▸ h.ksl, h.kslOk⟩

theorem SS.of_upd {r : Reg} {v : BitVec 64} (h : SS G STK σ c s) (u : Upd s t r v)
    (sp : t.sp = s.sp) (h28 : r ≠ .r28) : SS G STK σ c t :=
  h.of_keep (ws := [r]) ⟨fun r' hr' => u.other r' (by simpa using hr'), u.rd, u.wr⟩ u.mem sp
    (by simpa using h28.symm)

/-- Fewer header words, claims, arrays or key header words. -/
theorem SS.mono (h : SS G STK σ c s) {c' : Cfg} (hV : ∀ o ∈ c'.LS, o ∈ c.LS ∧ c.V o = c'.V o)
    (hcl : ∀ x ∈ c'.cl, x ∈ c.cl) (hA : ∀ j ∈ c'.live, j ∈ c.live ∧ c.A j = c'.A j)
    (hK : ∀ d ∈ c'.kls, d ∈ c.kls ∧ c.KV d = c'.KV d) : SS G STK σ c' s := by
  obtain ⟨gi, sb, clOk, arrs, liveOk, ksl, kslOk⟩ := h
  refine ⟨⟨gi.pre, gi.hG, gi.sp, gi.rd, gi.wr, gi.r28, gi.saved, gi.lr, gi.fixed, fun o ho => ?_,
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
    (h28 : .r28 ∉ ws := by decide) : SS G STK σ { c with cl := cl' } t := by
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
    · exact gi.scr_below (by omega_using [big, kb])
  -- The header: a step past it.
  have gi' : GI G STK σ c.V c.LS t := by
    have hd : ∀ q, q + 8 ≤ hEnd → ∀ r' ∈ G.rss os ++ [rBelow σ STK], (G.rs q 8).Disjoint r' := fun q hq r' hr' => by
      rcases mem r' hr' with ⟨p, hp, rfl⟩ | rfl
      · obtain ⟨a, _, b⟩ := hon' p hp; exact gi.sdisj (.inl (by omega_using [hq, a])) (by omega_using [hE, hq]) b
      · exact gi.scr_below (by omega_using [hE, hq])
    refine ⟨gi.pre, gi.hG, sp.trans gi.sp, r.2.1.trans gi.rd, r.2.2.trans gi.wr, (r.gpr h28).trans gi.r28,
      fun i hi => ?_, ?_, fun p hp => ?_, fun p hp => ?_, gi.ls, gi.frame.trans (f.sub fun x hx => ?_)⟩
    · rw [fw_frame f (hd _ (by simp only [hEnd]; omega_using [hi]))]; exact gi.saved i hi
    · rw [fw_frame f (hd _ (by decide))]; exact gi.lr
    · rw [fw_frame f (hd _ (by have := (fixed_ok G p hp).1; simp only [hEnd]; omega_using [this]))]; exact gi.fixed p hp
    · rw [fw_frame f (hd _ (by have := (gi.ls p hp).1; simp only [hEnd]; omega_using [this]))]; exact gi.slots p hp
    · rcases mem x hx with ⟨p, hp, rfl⟩ | rfl
      · exact ⟨G.rScr, List.mem_cons_self, sw G (hon' p hp).2.2⟩
      · exact ⟨rBelow σ STK, by simp, fun _ h => h⟩
  refine ⟨gi', fun x hx => ?_, fun x hx => ?_, fun j hj => ?_, h.liveOk, fun d hd => ?_, h.kslOk⟩
  · rcases hcl x hx with ⟨hm, ha⟩ | ⟨e, _⟩
    · obtain ⟨_, _, xb⟩ := h.clOk x hm
      rw [VG.Proof.Dsa.Generation.frame_bytesAt f (fun r' hr' => by
        rcases mem r' hr' with ⟨p, hp, rfl⟩ | rfl
        · exact gi.sdisj (ha p hp) xb (hon' p hp).2.2
        · exact gi.scr_below xb) (by omega_using [fit, xb])]
      exact h.sb x hm
    · exact e
  · rcases hcl x hx with ⟨hm, _⟩ | ⟨_, b⟩
    · exact h.clOk x hm
    · exact b
  · rw [num_frame h.lens f kd (h.liveOk j hj)]; exact h.arrs j hj
  · rw [slot_frame h.lens f kd (h.kslOk d hd)]; exact h.ksl d hd

/-- The volatile registers, which a call may change. -/
abbrev volatile : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

theorem keep_of_preserved {s t : State} (g : ∀ r ∈ preserved, t.gpr r = s.gpr r) (rd : t.rd = s.rd)
    (wr : t.wr = s.wr) : Keep volatile s t :=
  ⟨fun r hr => g r (by revert hr; cases r <;> decide), rd, wr⟩

/-- A step that writes the ranges `os` of `scratch` (past the header, apart
from the key working space), the header words `hw` (variable, not among
`LS`) and the stack below the stack pointer: the claims `cl'`, each kept and
apart from the ranges, or holding. -/
theorem SS.of_hdrScrs {ws : List Reg} (h : SS G STK σ c s) (r : Keep ws s t) (sp : t.sp = s.sp)
    {os : List (Nat × Nat)} (hon : ∀ p ∈ os, ClOk G (p.1, List.replicate p.2 0)) {hw : List Nat}
    (hhw : ∀ o ∈ hw, VarOk G o ∧ ∀ o' ∈ c.LS, o + 8 ≤ o' ∨ o' + 8 ≤ o)
    (f : Frame (G.rss os ++ hw.map (fun o => G.rs o 8) ++ [rBelow σ STK]) s.mem t.mem) {cl' : Claims}
    (hcl : ∀ x ∈ cl', x ∈ c.cl ∧ ∀ p ∈ os, Apart p.1 p.2 x)
    (h28 : .r28 ∉ ws := by decide) : SS G STK σ { c with cl := cl' } t := by
  have gi := h.gi
  have big := gi.wBig
  have kb := gi.kBig
  have fit := gi.scrFit
  have hE := gi.hEnd_le
  have hon' : ∀ p ∈ os, hEnd ≤ p.1 ∧ (p.1 + p.2 ≤ kB G.pLen ∨ wB G.pLen ≤ p.1) ∧ p.1 + p.2 ≤ G.scrLen * 8 :=
    fun p hp => by have := hon p hp; simp only [ClOk, List.length_replicate] at this; exact this
  have hw' : ∀ o ∈ hw, o + 8 ≤ fSave := fun o ho => (hhw o ho).1.1
  have mem : ∀ r' ∈ G.rss os ++ hw.map (fun o => G.rs o 8) ++ [rBelow σ STK],
      (∃ p ∈ os, r' = G.rs p.1 p.2) ∨ (∃ o ∈ hw, r' = G.rs o 8) ∨ r' = rBelow σ STK := fun r' hr' => by
    simp only [GP.rss, List.mem_append, List.mem_map, List.mem_singleton] at hr'
    rcases hr' with (⟨p, hp, rfl⟩ | ⟨o, ho, rfl⟩) | rfl
    · exact .inl ⟨p, hp, rfl⟩
    · exact .inr (.inl ⟨o, ho, rfl⟩)
    · exact .inr (.inr rfl)
  have kd : ∀ r' ∈ G.rss os ++ hw.map (fun o => G.rs o 8) ++ [rBelow σ STK],
      (⟨G.KB, kz G.pLen⟩ : Region).Disjoint r' := fun r' hr' => by
    rcases mem r' hr' with ⟨p, hp, rfl⟩ | ⟨o, ho, rfl⟩ | rfl
    · obtain ⟨_, a, b⟩ := hon' p hp; exact gi.kdisj a b
    · have := hw' o ho
      exact gi.kdisj (.inl (by simp only [kB, pB, fSave] at this ⊢; omega_using [this])) (by simp only [hEnd] at hE; omega_using [hE, this])
    · exact gi.scr_below (by omega_using [big, kb])
  -- The header word at `q`, apart from those written.
  have hd : ∀ q, q + 8 ≤ hEnd → (∀ o ∈ hw, o + 8 ≤ q ∨ q + 8 ≤ o) →
      ∀ r' ∈ G.rss os ++ hw.map (fun o => G.rs o 8) ++ [rBelow σ STK], (G.rs q 8).Disjoint r' :=
    fun q hq hq' r' hr' => by
      rcases mem r' hr' with ⟨p, hp, rfl⟩ | ⟨o, ho, rfl⟩ | rfl
      · obtain ⟨a, _, b⟩ := hon' p hp; exact gi.sdisj (.inl (by omega_using [hq, a])) (by omega_using [hE, hq]) b
      · have := hw' o ho
        exact gi.sdisj (hq' o ho).symm (by omega_using [hE, hq]) (by simp only [hEnd] at hE; omega_using [hE, this])
      · exact gi.scr_below (by omega_using [hE, hq])
  have fixedFar : ∀ p ∈ fixedWords G, ∀ o ∈ hw, o + 8 ≤ p.1 ∨ p.1 + 8 ≤ o := fun p hp o ho => by
    obtain ⟨_, a8, _, af⟩ := (hhw o ho).1
    obtain ⟨b, b8⟩ := fixed_ok G p hp
    have := af p hp; omega_using [a8, b8, this]
  have gi' : GI G STK σ c.V c.LS t := by
    refine ⟨gi.pre, gi.hG, sp.trans gi.sp, r.2.1.trans gi.rd, r.2.2.trans gi.wr, (r.gpr h28).trans gi.r28,
      fun i hi => ?_, ?_, fun p hp => ?_, fun p hp => ?_, gi.ls, gi.frame.trans (f.sub fun x hx => ?_)⟩
    · rw [fw_frame f (hd _ (by simp only [hEnd]; omega_using [hi]) fun o ho => by have := hw' o ho; simp only [fSave] at *; omega_using [this])]
      exact gi.saved i hi
    · rw [fw_frame f (hd _ (by decide) fun o ho => by
        obtain ⟨_, a8, aL, _⟩ := (hhw o ho).1; simp only [fLR] at aL ⊢; omega_using [a8, aL])]
      exact gi.lr
    · rw [fw_frame f (hd _ (by have := (fixed_ok G p hp).1; simp only [hEnd]; omega_using [this]) (fixedFar p hp))]
      exact gi.fixed p hp
    · rw [fw_frame f (hd _ (by have := (gi.ls p hp).1; simp only [hEnd]; omega_using [this]) fun o ho => (hhw o ho).2 p hp)]
      exact gi.slots p hp
    · rcases mem x hx with ⟨p, hp, rfl⟩ | ⟨o, ho, rfl⟩ | rfl
      · exact ⟨G.rScr, List.mem_cons_self, sw G (hon' p hp).2.2⟩
      · exact ⟨G.rScr, List.mem_cons_self, sw G (by have := hw' o ho; simp only [hEnd] at hE; omega_using [hE, this])⟩
      · exact ⟨rBelow σ STK, by simp, fun _ h => h⟩
  refine ⟨gi', fun x hx => ?_, fun x hx => h.clOk x (hcl x hx).1, fun j hj => ?_, h.liveOk, fun d hd' => ?_,
    h.kslOk⟩
  · obtain ⟨hm, ha⟩ := hcl x hx
    obtain ⟨xE, _, xb⟩ := h.clOk x hm
    rw [VG.Proof.Dsa.Generation.frame_bytesAt f (fun r' hr' => by
      rcases mem r' hr' with ⟨p, hp, rfl⟩ | ⟨o, ho, rfl⟩ | rfl
      · exact gi.sdisj (ha p hp) xb (hon' p hp).2.2
      · have := hw' o ho
        exact gi.sdisj (.inr (by simp only [hEnd] at xE; omega_using [xE, this])) xb (by simp only [hEnd] at hE; omega_using [hE, this])
      · exact gi.scr_below xb) (by omega_using [fit, xb])]
    exact h.sb x hm
  · rw [num_frame h.lens f kd (h.liveOk j hj)]; exact h.arrs j hj
  · rw [slot_frame h.lens f kd (h.kslOk d hd')]; exact h.ksl d hd'

/-- `c` with the header word `o` := `v`. -/
abbrev Cfg.setV (c : Cfg) (o : Nat) (v : BitVec 64) : Cfg := { c with V := upd c.V o v, LS := o :: c.LS }

/-- `std r, o(r28)` of a variable header word keeps the claims, arrays and key
header words. -/
theorem SS.stF (h : SS G STK σ c s) {o : Nat} (hv : VarOk G o) {r : Reg}
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, SS G STK σ (c.setV o (s.gpr r)) t → Mupd s t (s.mem.writeW (G.sa o) (s.gpr r)) → t.lr = s.lr →
      WP isa (.block rest) t Q) :
    WP isa (.block (st r o :: rest)) s Q := by
  refine h.gi.stF hv fun t gi m lr => k t ?_ m lr
  have gi₀ := h.gi
  have big := gi₀.wBig
  have kb := gi₀.kBig
  have hE := gi₀.hEnd_le
  obtain ⟨oS, _, _, _⟩ := hv
  have f : Frame [G.rs o 8] s.mem t.mem := by
    rw [m.mem]; exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  have hd : (G.rs o 8).Disjoint (⟨G.KB, kz G.pLen⟩ : Region) :=
    (gi₀.kdisj (o := o) (n := 8) (.inl (by simp only [kB, fSave] at oS ⊢; omega_using [oS]))
      (by simp only [hEnd] at hE; omega_using [hE, oS])).symm
  refine ⟨gi, h.sb.frame f (fun x hx r' hr' => ?_) (fun x hx => ?_), h.clOk, fun j hj => ?_, h.liveOk,
    fun d hd' => ?_, h.kslOk⟩
  · simp only [List.mem_singleton] at hr'; subst hr'
    obtain ⟨a, _, b⟩ := h.clOk x hx
    exact gi₀.sdisj (.inr (by simp only [hEnd] at a; omega_using [oS, a])) b (by simp only [hEnd] at hE; omega_using [hE, oS])
  · have := (h.clOk x hx).2.2; have := gi₀.scrFit; omega_arith
  · rw [num_frame h.lens f (fun r' hr' => by simp only [List.mem_singleton] at hr'; subst hr'; exact hd.symm)
      (h.liveOk j hj)]
    exact h.arrs j hj
  · rw [slot_frame h.lens f (fun r' hr' => by simp only [List.mem_singleton] at hr'; subst hr'; exact hd.symm)
      (h.kslOk d hd')]
    exact h.ksl d hd'

end

end VG.Proof.Dsa.PPC64LE.Gen

end

end

/-! ### `Dsa.PPC64LE.Gen.VP`, which only this module used -/

section

/-! # DSA parameter generation on PPC64LE: pieces proven correct and constant time at once

As on ARMv7 (`Proof/Rsa/Arm/RvVP.lean`): `VP F c G`: from any state at the
stage `F σ` of a run from `σ`, `c` ends at the stage `G σ` (`wp`), and two
runs, each at the stage `F` of its own run, leak the same trace and end at
the stages `G` (`ct`). The stages carry the public parameters both runs
share, so that a piece checked by the taint analysis needs only that the
registers it takes as public are determined by them (`VP.taint`), and pieces
compose by `seq`, `ite` and `loop` (whose number of iterations is public).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE

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
    (cert : ∃ hc, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs rs) c hc).isSome = true)
    (sp : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → s₁.sp = s₂.sp)
    (regs : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (wp : ∀ σ s, F σ s → WP isa c s (G σ)) : VP F c G := by
  obtain ⟨_, hc⟩ := cert
  exact of_ct (fun σ₁ σ₂ => RelCT.taint (A := VG.PPC64LE.taint) (Taint.ofRegs rs)
    (fun s t h => ⟨sp _ _ _ _ h.1 h.2, fun r hr => regs _ _ _ _ h.1 h.2 r
      (by simpa [Taint.ofRegs] using RegSet.mem_ofList.mp hr)⟩) hc) wp

/-- `taint`, with the Montgomery kernel's summary in place of its code
(`Proof/Bignum/PPC64LE/MontSum.lean`). -/
theorem taintR {c : Prog isa} (rs : List Reg)
    (cert : ∃ hc, (VG.Taint.checkR VG.PPC64LE.taint VG.Proof.Bignum.PPC64LE.montSums (Taint.ofRegs rs) c
      hc).isSome = true ∧ VG.Taint.fillR VG.Proof.Bignum.PPC64LE.montSums c hc = c)
    (sp : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → s₁.sp = s₂.sp)
    (regs : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (wp : ∀ σ s, F σ s → WP isa c s (G σ)) : VP F c G := by
  obtain ⟨_, hc, hf⟩ := cert
  exact of_ct (fun σ₁ σ₂ => RelCT.taintR VG.Proof.Bignum.PPC64LE.montSums_ok (Taint.ofRegs rs)
    (fun s t h => ⟨sp _ _ _ _ h.1 h.2, fun r hr => regs _ _ _ _ h.1 h.2 r
      (by simpa [Taint.ofRegs] using RegSet.mem_ofList.mp hr)⟩) hf hc) wp

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
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega_using [hp]⟩
      exact .inr ⟨by rw [he]; simp, k, by omega_using [], hi hp, uy⟩
  · refine RelCT.loop (M := isa) (fun m => Two (Sy (I (m + 1)))) (fun m => ?_) n
    refine (hb m).ct.mono (fun _ _ h => h) fun s₁ s₂ ⟨σ₁, σ₂, ⟨⟨e₁, q₁, i₁⟩, y₁⟩, ⟨⟨e₂, q₂, i₂⟩, y₂⟩⟩ =>
      ⟨e₁.trans e₂.symm, fun hf => ?_, fun ht => ?_⟩
    · have h0 : m = 0 := by rw [e₁] at hf; simpa using hf
      exact ⟨σ₁, σ₂, ⟨q₁ h0, y₁⟩, ⟨q₂ h0, y₂⟩⟩
    · have hp : 0 < m := by rw [e₁] at ht; simpa using ht
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega_using [hp]⟩
      exact ⟨k, by omega_using [], σ₁, σ₂, ⟨i₁ hp, y₁⟩, ⟨i₂ hp, y₂⟩⟩

/-- A piece no state reaches. -/
theorem of_false {c : Prog isa} (h : ∀ σ s, ¬ F σ s) : VP F c G :=
  ⟨fun σ s hs => absurd hs (h σ s), fun _ _ _ _ _ _ ⟨σ, _, h₁, _⟩ => absurd h₁.1 (h σ _)⟩

end VP

end VG.Proof.Dsa.PPC64LE.Gen

end

end


/-! # DSA parameter generation on PPC64LE: header words in pieces

`WP.wr`: an instruction that writes one register, with the stack pointer and
the link register kept. The taint analysis does not follow the header's
words, which the search keeps its state in: a load of one (`ld`) and a store
into one (`st`) leak only addresses from `r28`, which holds `scratch` in both
runs of the search, so they are analysed with `r28` public (`ld_vp`,
`st_vp`, `stImm_vp`, `cmpF_vp`), and the code between them with the registers
the loads set public (`VP.taint`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

/-- An instruction that writes `v` to `d`. -/
theorem WP.wr {i : Instr} {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {v : BitVec 64}
    (h : exec i s = some (s.write d v))
    (k : ∀ s', Upd s s' d v → s'.sp = s.sp → s'.lr = s.lr → WP isa (.block is) s' Q) :
    WP isa (.block (i :: is)) s Q :=
  WP.cons h (k _ (Upd.write _ _ _) rfl rfl)

section
variable {G : GP} {STK : Nat}

/-- The stage's states hold `scratch` in `r28` and have the call's stack pointer. -/
abbrev Pub (G : GP) (F : State → State → Prop) : Prop :=
  ∀ σ s, F σ s → s.gpr .r28 = G.scr ∧ s.sp = G.sp

theorem SS.pub {F : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s) :
    Pub G F := fun σ s h => ⟨(hF σ s h).gi.r28, by rw [(hF σ s h).gi.sp, ← (hF σ s h).gi.hG]; rfl⟩

/-- A piece analysed with `r28` and `rs` public. -/
theorem VP.pub {F Q : State → State → Prop} {c : Prog isa} (hp : Pub G F) (rs : List Reg)
    (cert : ∃ hc, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs (.r28 :: rs)) c hc).isSome = true)
    (regs : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (wp : ∀ σ s, F σ s → WP isa c s (Q σ)) : VP F c Q :=
  VP.taint (.r28 :: rs) cert (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [(hp _ _ h₁).2, (hp _ _ h₂).2])
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [(hp _ _ h₁).1, (hp _ _ h₂).1]
      · exact regs _ _ _ _ h₁ h₂ r hr) wp

end

/-- `ld t, o(r28)` of a header word whose value `v` is known, keeping a stage. -/
theorem SS.ldK {G : GP} {STK : Nat} {σ s : State} {c : Cfg} (h : SS G STK σ c s) {o : Nat} (ho : o + 8 ≤ hEnd)
    (h8 : o % 8 = 0) {v : BitVec 64} (hv : fw s.mem G o = v) {t : Reg} (ht : t ≠ .r28) {rest : List Instr}
    {Q : State → Prop} (k : ∀ s', SS G STK σ c s' → Upd s s' t v → WP isa (.block rest) s' Q) :
    WP isa (.block (ld t o :: rest)) s Q := by
  have hE := h.gi.hEnd_le
  refine WP.cons (s' := s.write t v) ?_ (k _ (h.of_upd (Upd.write _ _ _) rfl ht) (Upd.write _ _ _))
  rw [show ld t o = .load .d t .r28 o from rfl, exec_load_d (by decide) ⟨by simp only [hEnd, fSave] at ho; omega_using [ho],
    by omega_using [h8]⟩ (by rw [h.gi.r28]; exact h.gi.inRdWr (by omega_using [ho, hE])), h.gi.r28, ← hv]

/-! ## Header words as pieces -/

section
variable {G : GP} {STK : Nat}

/-- A load of a header word whose value both runs know. -/
theorem ld_vp {P Q : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, P σ s → SS G STK σ (c σ) s)
    {r : Reg} (hr : r ≠ .r28) {o : Nat} (ho : o + 8 ≤ hEnd) (h8 : o % 8 = 0) {x : BitVec 64}
    (hx : ∀ σ s, P σ s → fw s.mem G o = x)
    (k : ∀ σ s t, P σ s → SS G STK σ (c σ) t → Upd s t r x → Q σ t) : VP P (.block [ld r o]) Q := by
  refine VP.pub (SS.pub hF) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28]) (.block [ld r o]),
    by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  have h := hF σ s hs
  have hE := h.gi.hEnd_le
  refine WP.cons (s' := s.write r x) ?_ (WP.block_nil (k σ s _ hs (h.of_upd (Upd.write _ _ _) rfl hr)
    (Upd.write _ _ _)))
  rw [show ld r o = .load .d r .r28 o from rfl, exec_load_d (by decide) ⟨by simp only [hEnd, fSave] at ho; omega_using [ho],
    by omega_using [h8]⟩ (by rw [h.gi.r28]; exact h.gi.inRdWr (by omega_using [ho, hE])), h.gi.r28, ← hx σ s hs]

/-- A store into a variable word of the header. -/
theorem st_vp {P Q : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, P σ s → SS G STK σ (c σ) s)
    {r : Reg} {o : Nat} (hv : VarOk G o)
    (k : ∀ σ s t, P σ s → SS G STK σ ((c σ).setV o (s.gpr r)) t → Keep [] s t → Q σ t) :
    VP P (.block [st r o]) Q := by
  refine VP.pub (SS.pub hF) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28]) (.block [st r o]),
    by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  exact (hF σ s hs).stF hv fun t h m _ => WP.block_nil (k σ s t hs h ⟨fun r _ => by rw [m.gpr], m.rd, m.wr⟩)

/-- `stImm o v`: the header word `o` := `v`. -/
theorem stImm_vp {P Q : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, P σ s → SS G STK σ (c σ) s)
    {o v : Nat} (hv : v < 2 ^ 15) (ho : VarOk G o)
    (k : ∀ σ s t, P σ s → SS G STK σ ((c σ).setV o (BitVec.ofNat 64 v)) t → Keep [.r3] s t → Q σ t) :
    VP P (.block (stImm o v)) Q := by
  refine VP.pub (SS.pub hF) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28]) (.block (stImm o v)),
    by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  refine WP.wr (d := .r3) (exec_li hv) fun s₁ u₁ sp₁ _ => ?_
  have h₁ : SS G STK σ (c σ) s₁ := (hF σ s hs).of_upd u₁ sp₁ (by decide)
  refine h₁.stF ho fun t h m _ => WP.block_nil (k σ s t hs (by rw [u₁.gpr] at h; exact h) ?_)
  exact ⟨fun r hr => by rw [m.gpr, u₁.other _ (by simpa using hr)], by rw [m.rd, u₁.rd], by rw [m.wr, u₁.wr]⟩

theorem sub_beq_zero (x y : BitVec 64) : (x - y == 0) = (x == y) := by
  by_cases h : x = y
  · subst h; simp
  · have : x - y ≠ 0 := fun e => h (by rw [← BitVec.sub_add_cancel x y, e]; exact BitVec.zero_add y)
    rw [beq_false_of_ne this, beq_false_of_ne h]

/-- `cmpF o v`: `r0 = 0` iff the header word `o`, which both runs know, is `v`. -/
theorem cmpF_vp {P Q : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, P σ s → SS G STK σ (c σ) s)
    {o v : Nat} (ho : o + 8 ≤ hEnd) (h8 : o % 8 = 0) (hv : v ≤ 2 ^ 15) {x : BitVec 64}
    (hx : ∀ σ s, P σ s → fw s.mem G o = x)
    (k : ∀ σ s t, P σ s → SS G STK σ (c σ) t → Keep [.r0, .r3] s t →
      isa.eval (.zero .d .r0) t = some (x == BitVec.ofNat 64 v) → Q σ t) : VP P (.block (cmpF o v)) Q := by
  refine VP.pub (SS.pub hF) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28]) (.block (cmpF o v)),
    by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  have h := hF σ s hs
  have hE := h.gi.hEnd_le
  refine WP.cons (s' := s.write .r3 x) ?_ ?_
  · rw [show ld .r3 o = .load .d .r3 .r28 o from rfl, exec_load_d (by decide)
      ⟨by simp only [hEnd, fSave] at ho; omega_using [ho], by omega_using [h8]⟩ (by rw [h.gi.r28]; exact h.gi.inRdWr (by omega_using [ho, hE])),
      h.gi.r28, ← hx σ s hs]
  refine WP.wr (exec_subi (by decide) hv) fun t u sp _ => WP.block_nil ?_
  have u₀ : Upd s (s.write .r3 x) .r3 x := Upd.write _ _ _
  refine k σ s t hs ((h.of_upd u₀ rfl (by decide)).of_upd u sp (by decide)) ?_ ?_
  · exact ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u.other _ hr.1, u₀.other _ hr.2], by rw [u.rd, u₀.rd], by rw [u.wr, u₀.wr]⟩
  · rw [eval_zero, u.gpr, u₀.gpr, sub_beq_zero]

/-- `ltR`: `r0 = 0` iff `r3 < r4`, through the carry. -/
theorem ltR_ok {s : State} {rest : List Instr} {Q : State → Prop} {x y : BitVec 64} (h3 : s.gpr .r3 = x)
    (h4 : s.gpr .r4 = y)
    (k : ∀ t, Keep [.r0] s t → t.mem = s.mem → t.sp = s.sp → t.lr = s.lr →
      isa.eval (.zero .d .r0) t = some (decide (x.toNat < y.toNat)) → WP isa (.block rest) t Q) :
    WP isa (.block (ltR ++ rest)) s Q := by
  refine WP.cons exec_subc (WP.cons (exec_li (by decide)) (WP.cons exec_addze (k _ ?_ rfl rfl rfl ?_)))
  · refine ⟨fun r hr => ?_, rfl, rfl⟩
    have : r ≠ .r0 := by simpa using hr
    simp [State.writeCarry, State.write, this]
  · rw [eval_zero]
    simp only [State.writeCarry, State.write, ite_true, h3, h4]
    have hx := x.isLt
    have hy := y.isLt
    by_cases hl : x.toNat < y.toNat
    · simp [show ¬(2 ^ 64 ≤ x.toNat + (2 ^ 64 - 1 - y.toNat) + 1) by omega_using [hl], hl]
    · simp [show 2 ^ 64 ≤ x.toNat + (2 ^ 64 - 1 - y.toNat) + 1 by omega_using [hl], hl]

/-- `ld r3, o(r28); li r4, v; ltR`: `r0 = 0` iff the header word `o`, which
both runs know, is below `v`. -/
theorem ltF_vp {P Q : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, P σ s → SS G STK σ (c σ) s)
    {o v : Nat} (ho : o + 8 ≤ hEnd) (h8 : o % 8 = 0) (hv : v < 2 ^ 15) {x : BitVec 64}
    (hx : ∀ σ s, P σ s → fw s.mem G o = x)
    (k : ∀ σ s t, P σ s → SS G STK σ (c σ) t → Keep [.r0, .r3, .r4] s t →
      isa.eval (.zero .d .r0) t = some (decide (x.toNat < v)) → Q σ t) :
    VP P (.block ([ld .r3 o, .li .r4 v] ++ ltR)) Q := by
  refine VP.pub (SS.pub hF) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
    (.block ([ld .r3 o, .li .r4 v] ++ ltR)), by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp))
    fun σ s hs => ?_
  have h := hF σ s hs
  refine h.ldK ho h8 (hx σ s hs) (by decide) fun s₁ h₁ u₁ => ?_
  refine WP.wr (d := .r4) (exec_li hv) fun s₂ u₂ sp₂ _ => ?_
  have h₂ := h₁.of_upd u₂ sp₂ (by decide)
  refine ltR_ok (by rw [u₂.other _ (by decide), u₁.gpr]) u₂.gpr fun t K m sp _ e => WP.block_nil ?_
  refine k σ s t hs (h₂.of_keep K m sp) ⟨fun r hr => ?_, by rw [K.2.1, u₂.rd, u₁.rd], by rw [K.2.2, u₂.wr, u₁.wr]⟩ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [K.gpr (by simpa using hr.1), u₂.other _ hr.2.2, u₁.other _ hr.2.1]
  · rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hv])]

/-- An instruction that writes one register other than `r28` keeps a stage. -/
theorem SS.wrK {σ s : State} {c : Cfg} (h : SS G STK σ c s) {i : Instr} {d : Reg} {v : BitVec 64}
    (he : exec i s = some (s.write d v)) (hd : d ≠ .r28 := by decide) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', SS G STK σ c s' → Upd s s' d v → WP isa (.block rest) s' Q) : WP isa (.block (i :: rest)) s Q :=
  WP.wr he fun s' u sp _ => k s' (h.of_upd u sp hd) u

/-- `shl`: `r := v · 2^sh`. -/
theorem shl_ok {σ s : State} {c : Cfg} (h : SS G STK σ c s) {r : Reg} (hr : r ≠ .r28) {v sh : Nat}
    (hv : v < 2 ^ 15) (hsh : sh < 64) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', SS G STK σ c s' → Keep [r] s s' → s'.gpr r = BitVec.ofNat 64 (v * 2 ^ sh) → s'.mem = s.mem →
      WP isa (.block rest) s' Q) : WP isa (.block (shl r v sh ++ rest)) s Q := by
  refine h.wrK (exec_li hv) hr fun s₁ h₁ u₁ => h₁.wrK (exec_lsl hsh) hr fun s₂ h₂ u₂ => k s₂ h₂
    ⟨fun r' hr' => by rw [u₂.other _ (by simpa using hr'), u₁.other _ (by simpa using hr')],
      by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩ ?_ (by rw [u₂.mem, u₁.mem])
  rw [u₂.gpr, u₁.gpr]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (show v < 2 ^ 64 by omega_using [hv])]

/-- `ld r3, o(r28); shl r4 v sh; ltR`: `r0 = 0` iff the header word `o` is
below `v · 2^sh`. -/
theorem ltShl_vp {P Q : State → State → Prop} {c : State → Cfg} (hF : ∀ σ s, P σ s → SS G STK σ (c σ) s)
    {o v sh : Nat} (ho : o + 8 ≤ hEnd) (h8 : o % 8 = 0) (hv : v < 2 ^ 15) (hsh : sh < 64)
    (hb : v * 2 ^ sh < 2 ^ 64) {x : BitVec 64} (hx : ∀ σ s, P σ s → fw s.mem G o = x)
    (k : ∀ σ s t, P σ s → SS G STK σ (c σ) t → Keep [.r0, .r3, .r4] s t →
      isa.eval (.zero .d .r0) t = some (decide (x.toNat < v * 2 ^ sh)) → Q σ t) :
    VP P (.block ([ld .r3 o] ++ shl .r4 v sh ++ ltR)) Q := by
  refine VP.pub (SS.pub hF) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
    (.block ([ld .r3 o] ++ shl .r4 v sh ++ ltR)), by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp))
    fun σ s hs => ?_
  have h := hF σ s hs
  rw [List.append_assoc]
  refine h.ldK ho h8 (hx σ s hs) (by decide) fun s₁ h₁ u₁ => ?_
  refine shl_ok h₁ (r := .r4) (by decide) hv hsh fun s₂ h₂ K₂ e₂ m₂ => ?_
  refine ltR_ok (by rw [K₂.gpr (by decide), u₁.gpr]) e₂ fun t K m sp _ e => WP.block_nil ?_
  refine k σ s t hs (h₂.of_keep K m sp) ⟨fun r hr => ?_, by rw [K.2.1, K₂.2.1, u₁.rd], by rw [K.2.2, K₂.2.2, u₁.wr]⟩ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [K.gpr (by simpa using hr.1), K₂.gpr (by simpa using hr.2.2), u₁.other _ hr.2.1]
  · rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]

end

end VG.Proof.Dsa.PPC64LE.Gen

end

end

/-! # DSA parameter generation on PPC64LE: byte loops

`loop_nz`: a `do … while (r ≠ 0)` loop that runs its body `N` times.
`copyLoop_ok`: `copyBody`'s loop copies `n` bytes from `r3` to `r4`, which
are apart. `zeroLoop_ok`: `zeroN`'s loop zeroes `n` bytes from `r3`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

/-- A `do … while (r ≠ 0)` loop whose body runs `N` times: iteration `i`
keeps the invariant, and leaves `r` zero exactly when it is the last. -/
theorem loop_nz {body : Prog isa} {r : Reg} {Q : State → Prop} (Inv : Nat → State → Prop) {N : Nat}
    (hN : 0 < N)
    (hstep : ∀ i < N, ∀ s, Inv i s →
      WP isa body s (fun s' => Inv (i + 1) s' ∧ (s'.gpr r != 0) = decide (i + 1 ≠ N)))
    (hQ : ∀ s, Inv N s → Q s) {s₀ : State} (h0 : Inv 0 s₀) : WP isa (.loop body (.nonzero .d r)) s₀ Q := by
  let I : Nat → State → Prop := fun n s => ∃ i, i < N ∧ n = N - i ∧ Inv i s
  have hI : I N s₀ := ⟨0, hN, (Nat.sub_zero N).symm, h0⟩
  refine WP.loop (M := isa) (body := body) (c := .nonzero .d r) (Q := Q) I ?_ N s₀ hI
  rintro n s ⟨i, hi, rfl, hs⟩
  refine WP.mono (hstep i hi s hs) fun s' ⟨hs', hz⟩ => ?_
  have ev : isa.eval (.nonzero .d r) s' = some (decide (i + 1 ≠ N)) := by
    rw [eval_nonzero]; simpa using hz
  by_cases h : i + 1 = N
  · refine .inl ⟨by rw [ev]; simp [h], hQ s' (h ▸ hs')⟩
  · exact .inr ⟨by rw [ev]; simp [h], N - (i + 1), by omega_using [hi], i + 1, by omega_using [hi, h], rfl, hs'⟩

/-- The count after `subi r, r, 1` from `N - i`. -/
theorem count_sub {N i : Nat} (hi : i < N) :
    BitVec.ofNat 64 (N - i) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (N - (i + 1)) := by
  rw [show N - i = (N - (i + 1)) + 1 by omega_using [hi], BitVec.ofNat_add, BitVec.add_sub_cancel]

/-- The count is nonzero exactly when it is not the last iteration. -/
theorem count_nz {N i : Nat} (hi : i < N) (hN : N < 2 ^ 64) :
    (BitVec.ofNat 64 (N - (i + 1)) != 0) = decide (i + 1 ≠ N) := by
  by_cases h : i + 1 = N
  · subst h; simp
  · have h1 : (BitVec.ofNat 64 (N - (i + 1))).toNat = N - (i + 1) := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [hN])
    have : BitVec.ofNat 64 (N - (i + 1)) ≠ 0 := fun e => by
      have := congrArg BitVec.toNat e; rw [h1] at this; simp at this; omega_using [hi, h, this]
    rw [bne_iff_ne.mpr this]; simp [h]

theorem ptr_succ1 (p : BitVec 64) (i : Nat) :
    p + BitVec.ofNat 64 i + BitVec.ofNat 64 1 = p + BitVec.ofNat 64 (i + 1) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-! ## Copies -/

/-- After copying `k` bytes of `len` from `S` to `D`. -/
structure CopyInv (S D : Addr) (len : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  r3 : s.gpr .r3 = S + BitVec.ofNat 64 k
  r4 : s.gpr .r4 = D + BitVec.ofNat 64 k
  r5 : s.gpr .r5 = BitVec.ofNat 64 (len - k)
  keep : Keep [.r3, .r4, .r5, .r6] s₀ s
  sp : s.sp = s₀.sp
  frame : Frame [⟨D, len⟩] s₀.mem s.mem
  bytes : ∀ t < k, s.mem (D + BitVec.ofNat 64 t) = s₀.mem (S + BitVec.ofNat 64 t)

theorem copy_step {S D : Addr} {len : Nat} {s₀ : State} (hlen : len < 2 ^ 64)
    (hd : (⟨S, len⟩ : Region).Disjoint ⟨D, len⟩)
    (cr : ∀ k < len, InRegions (s₀.rd ++ s₀.wr) (S + BitVec.ofNat 64 k) 1)
    (cw : ∀ k < len, InRegions s₀.wr (D + BitVec.ofNat 64 k) 1)
    {k : Nat} (hk : k < len) {s : State} (h : CopyInv S D len s₀ k s) :
    WP isa (.block VG.Impl.MlKem.PPC64LE.copyBody) s fun s' =>
      CopyInv S D len s₀ (k + 1) s' ∧ (s'.gpr .r5 != 0) = decide (k + 1 ≠ len) := by
  have cS : (⟨S, len⟩ : Region).Contains (S + BitVec.ofNat 64 k) 1 := Offset.contains_base _ (by omega_using [hk]) (by omega_using [hlen, hk])
  have cD : (⟨D, len⟩ : Region).Contains (D + BitVec.ofNat 64 k) 1 := Offset.contains_base _ (by omega_using [hk]) (by omega_using [hlen, hk])
  refine WP.sp_eq ?_
  simp only [VG.Impl.MlKem.PPC64LE.copyBody]
  refine wp_lbz (by decide) (by decide) (by rw [h.r3, BitVec.add_zero]) (by rw [h.keep.2.1, h.keep.2.2]; exact cr k hk)
    fun s₁ u₁ => ?_
  refine wp_stb (by decide) (by decide) (by rw [u₁.other _ (by decide), h.r4, BitVec.add_zero])
    (by rw [u₁.wr, h.keep.2.2]; exact cw k hk) fun s₂ m₂ => ?_
  refine WP.wr (exec_addi (by decide) (by decide)) fun s₃ u₃ sp₃ _ => ?_
  refine WP.wr (exec_addi (by decide) (by decide)) fun s₄ u₄ sp₄ _ => ?_
  refine WP.wr (exec_subi (by decide) (by decide)) fun s₅ u₅ sp₅ _ => WP.block_nil fun sp => ⟨⟨?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, m₂.gpr, u₁.other _ (by decide), h.r3, ptr_succ1]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide), h.r4, ptr_succ1]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide), h.r5,
      count_sub hk]
  · refine ⟨fun r hr => ?_, by rw [u₅.rd, u₄.rd, u₃.rd, m₂.rd, u₁.rd, h.keep.2.1],
      by rw [u₅.wr, u₄.wr, u₃.wr, m₂.wr, u₁.wr, h.keep.2.2]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₅.other _ hr.2.2.1, u₄.other _ hr.2.1, u₃.other _ hr.1, m₂.gpr, u₁.other _ hr.2.2.2,
      h.keep.1 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2])]
  · rw [sp, h.sp]
  · rw [u₅.mem, u₄.mem, u₃.mem, m₂.mem, u₁.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _ cD
  · intro t ht
    rw [u₅.mem, u₄.mem, u₃.mem, m₂.mem, u₁.mem, write1_apply, u₁.gpr, setWidth8_64]
    by_cases e : t = k
    · subst e
      rw [ite_eq_left (by simp)]
      exact h.frame _ fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hd _ cS
    · have hne : ¬ ((D + BitVec.ofNat 64 t - (D + BitVec.ofNat 64 k)).toNat < 1) := by
        intro hlt
        have e0 : D + BitVec.ofNat 64 t - (D + BitVec.ofNat 64 k) = 0 :=
          BitVec.eq_of_toNat_eq (by have : (0 : BitVec 64).toNat = 0 := rfl; omega)
        apply Offset.add_ofNat_ne D (a := t) (b := k) (by omega_using [hlen, hk, ht]) (by omega_using [hlen, hk]) e
        rw [← BitVec.sub_add_cancel (D + BitVec.ofNat 64 t) (D + BitVec.ofNat 64 k), e0]; simp
      rw [ite_eq_right hne]; exact h.bytes t (by omega_using [ht, e])
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide), h.r5,
      count_sub hk]
    exact count_nz hk hlen

/-- `len > 0` bytes copied from `S` to `D`, with the pointers and the count in
`r3`–`r5`. -/
theorem copyLoop_ok {S D : Addr} {len : Nat} {s₀ : State} (hlen : len < 2 ^ 64) (hl0 : 0 < len)
    (hd : (⟨S, len⟩ : Region).Disjoint ⟨D, len⟩)
    (cr : ∀ k < len, InRegions (s₀.rd ++ s₀.wr) (S + BitVec.ofNat 64 k) 1)
    (cw : ∀ k < len, InRegions s₀.wr (D + BitVec.ofNat 64 k) 1)
    (h3 : s₀.gpr .r3 = S) (h4 : s₀.gpr .r4 = D) (h5 : s₀.gpr .r5 = BitVec.ofNat 64 len) :
    WP isa (.loop (.block VG.Impl.MlKem.PPC64LE.copyBody) (.nonzero .d .r5)) s₀ fun s =>
      Keep [.r3, .r4, .r5, .r6] s₀ s ∧ s.sp = s₀.sp ∧ Frame [⟨D, len⟩] s₀.mem s.mem ∧
      Spec.Rsa.bytesAt s.mem D len = Spec.Rsa.bytesAt s₀.mem S len :=
  loop_nz (CopyInv S D len s₀) hl0 (fun k hk s h => copy_step hlen hd cr cw hk h)
    (fun s h => ⟨h.keep, h.sp, h.frame, by
      simp only [Spec.Rsa.bytesAt]
      exact List.map_congr_left fun t ht => h.bytes t (List.mem_range.mp ht)⟩)
    ⟨by rw [h3]; simp, by rw [h4]; simp, by rw [h5]; simp, Keep.refl _ _, rfl, Frame.refl _ _,
      fun t ht => absurd ht (Nat.not_lt_zero t)⟩

/-! ## Copies as pieces -/

theorem GP.sa_add (G : GP) (o i : Nat) : G.sa o + BitVec.ofNat 64 i = G.sa (o + i) := by
  simp only [GP.sa, BitVec.add_assoc, ← BitVec.ofNat_add]

open GP (sa_add) in

section
variable {G : GP} {STK : Nat}

/-- A copy between two ranges of `scratch` past the header, apart from the key
working space and from each other: the claims `cl'` apart from the
destination kept, the destination's bytes those of the source. -/
theorem copyS_vp {F Q : State → State → Prop} {c : State → Cfg} {dst src n : Nat}
    (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s) (hn : 0 < n) (hn15 : n < 2 ^ 15) (hd15 : dst < 2 ^ 15)
    (hs15 : src < 2 ^ 15) (hdo : ∀ σ s, F σ s → ClOk G (dst, List.replicate n 0))
    (hso : ∀ σ s, F σ s → src + n ≤ G.scrLen * 8)
    (hsep : dst + n ≤ src ∨ src + n ≤ dst)
    (k : ∀ σ s t, F σ s → SS G STK σ { c σ with cl := (c σ).cl.filter fun x => decide (Apart dst n x) } t →
      Keep [.r3, .r4, .r5, .r6] s t →
      Spec.Rsa.bytesAt t.mem (G.sa dst) n = Spec.Rsa.bytesAt s.mem (G.sa src) n → Q σ t) :
    VP F (copyS dst src n) Q := by
  refine VP.pub (SS.pub hF) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
    (copyS 512 576 8), by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  have h := hF σ s hs
  have gi := h.gi
  have fit := gi.scrFit
  obtain ⟨dE, dK, dS⟩ := hdo σ s hs
  simp only [List.length_replicate] at dK dS
  have sS := hso σ s hs
  refine WP.sp_eq ?_
  simp only [copyS, copyN, List.cons_append, List.nil_append]
  refine WP.seq ?_
  refine WP.wr (exec_addi (by decide) hs15) fun s₁ u₁ _ _ => ?_
  refine WP.wr (exec_addi (by decide) hd15) fun s₂ u₂ _ _ => ?_
  refine WP.wr (exec_li hn15) fun s₃ u₃ _ _ => WP.block_nil ?_
  have r28 : s.gpr .r28 = G.scr := gi.r28
  have rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine WP.mono (copyLoop_ok (S := G.sa src) (D := G.sa dst) (by omega_using [hn15]) hn
    (gi.sdisj hsep.symm (by omega_using [sS]) (by omega_using [dS]))
    (fun i hi => by rw [rd₃, wr₃, sa_add]; exact gi.inRdWr (o := src + i) (n := 1) (by omega_using [sS, hi]))
    (fun i hi => by rw [wr₃, sa_add]; exact gi.inScr (o := dst + i) (n := 1) (by omega_using [dS, hi]))
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, r28])
    (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), r28]) (by rw [u₃.gpr]))
    fun t ⟨kp, sp', f, b⟩ sp => ?_
  have K : Keep [.r3, .r4, .r5, .r6] s t := by
    refine ⟨fun r hr => ?_, by rw [kp.2.1, rd₃], by rw [kp.2.2, wr₃]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [kp.1 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]), u₃.other _ hr.2.2.1, u₂.other _ hr.2.1,
      u₁.other _ hr.1]
  refine k σ s t hs ?_ K (by rw [b, m₃])
  refine h.of_scrs (os := [(dst, n)]) K sp (fun p hp => by
      simp only [List.mem_singleton] at hp; subst hp; exact ⟨dE, by simpa using dK, by simpa using dS⟩)
    (by rw [← m₃]; exact f.mono fun r hr => by simp at hr ⊢; exact .inl hr) fun x hx => .inl ?_
  obtain ⟨hm, ha⟩ := List.mem_filter.mp hx
  exact ⟨hm, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; simpa using ha⟩

/-- A copy of `n` bytes from the pointer `P` in the header word `o` (to a
region apart from `scratch` and the stack below the stack pointer, readable)
to a range of `scratch` past the header, apart from the key working space:
the claims `cl'` apart from the destination kept, the destination's bytes
those at `P`. -/
theorem copyIn_vp {F Q : State → State → Prop} {c : State → Cfg} {o dst n : Nat} {P : Addr}
    (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s) (hn : 0 < n) (hn15 : n < 2 ^ 15) (hd15 : dst < 2 ^ 15)
    (ho : o + 8 ≤ hEnd) (h8 : o % 8 = 0) (hP : ∀ σ s, F σ s → fw s.mem G o = P)
    (hdo : ∀ σ s, F σ s → ClOk G (dst, List.replicate n 0))
    (hPr : ∀ σ s, F σ s → InRegions (s.rd ++ s.wr) P n ∧ P.toNat + n ≤ 2 ^ 64 ∧
      (⟨P, n⟩ : Region).Disjoint G.rScr)
    (k : ∀ σ s t, F σ s → SS G STK σ { c σ with cl := (c σ).cl.filter fun x => decide (Apart dst n x) } t →
      Keep [.r3, .r4, .r5, .r6] s t →
      Spec.Rsa.bytesAt t.mem (G.sa dst) n = Spec.Rsa.bytesAt s.mem P n → Q σ t) :
    VP F (copyN [ld .r3 o] [scr .r4 dst] n) Q := by
  let M : State → State → Prop := fun σ t => ∃ s, F σ s ∧ SS G STK σ (c σ) t ∧ Keep [.r3, .r4, .r5] s t ∧
    t.sp = s.sp ∧ t.mem = s.mem ∧ t.gpr .r3 = P ∧ t.gpr .r4 = G.sa dst ∧ t.gpr .r5 = BitVec.ofNat 64 n
  refine VP.seq (G := M) (VP.pub (SS.pub hF) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
    (.block ([ld .r3 o] ++ [scr .r4 dst] ++ [.li .r5 n])), by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp))
    fun σ s hs => ?_) (VP.pub (G := G) (fun σ t ⟨_, _, h, _⟩ => ⟨h.gi.r28, by
      rw [h.gi.sp, ← h.gi.hG]; rfl⟩) [.r3, .r4, .r5] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
      (Taint.ofRegs [.r28, .r3, .r4, .r5]) (.loop (.block VG.Impl.MlKem.PPC64LE.copyBody) (.nonzero .d .r5)), by kernel_rfl⟩
    (fun σ₁ σ₂ s₁ s₂ ⟨_, _, _, _, _, _, a3, a4, a5⟩ ⟨_, _, _, _, _, _, b3, b4, b5⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a3, b3]
      · rw [a4, b4]
      · rw [a5, b5]) fun σ t ⟨s, hs, h, K₁, sp₁, m₁, t3, t4, t5⟩ => ?_)
  · have h := hF σ s hs
    have hE := h.gi.hEnd_le
    simp only [List.cons_append, List.nil_append]
    refine WP.cons (s' := s.write .r3 P) ?_ ?_
    · rw [show ld .r3 o = .load .d .r3 .r28 o from rfl, exec_load_d (by decide)
        ⟨by simp only [hEnd, fSave] at ho; omega_using [ho], by omega_using [h8]⟩ (by rw [h.gi.r28]; exact h.gi.inRdWr (by omega_using [ho, hE])),
        h.gi.r28, ← hP σ s hs]
    have u₁ : Upd s (s.write .r3 P) .r3 P := Upd.write _ _ _
    refine WP.wr (exec_addi (by decide) hd15) fun s₂ u₂ sp₂ _ => ?_
    refine WP.wr (exec_li hn15) fun s₃ u₃ sp₃ _ => WP.block_nil ⟨s, hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact ((h.of_upd u₁ rfl (by decide)).of_upd u₂ sp₂ (by decide)).of_upd u₃ sp₃ (by decide)
    · refine ⟨fun r hr => ?_, by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr]⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u₃.other _ hr.2.2, u₂.other _ hr.2.1, u₁.other _ hr.1]
    · rw [sp₃, sp₂]; rfl
    · rw [u₃.mem, u₂.mem, u₁.mem]
    · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
    · rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.gi.r28]
    · rw [u₃.gpr]
  have h₀ := hF σ s hs
  have gi := h₀.gi
  have fit := gi.scrFit
  obtain ⟨dE, dK, dS⟩ := hdo σ s hs
  simp only [List.length_replicate] at dK dS
  obtain ⟨Pr, Pf, Pd⟩ := hPr σ s hs
  have dsub : Region.Sub (G.rs dst n) G.rScr := sw G dS
  refine WP.sp_eq (WP.mono (copyLoop_ok (S := P) (D := G.sa dst) (by omega_using [hn15]) hn (Pd.sub_right dsub)
    (fun i hi => ?_) (fun i hi => by rw [K₁.2.2, sa_add]; exact gi.inScr (o := dst + i) (n := 1) (by omega_using [dS, hi]))
    t3 t4 t5) fun u ⟨kp, sp', f, b⟩ sp => ?_)
  · rw [K₁.2.1, K₁.2.2]
    obtain ⟨r, hr, hc⟩ := Pr
    have hb : (P + BitVec.ofNat 64 i - P).toNat < n := by
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hn15, hi])]; exact hi
    exact ⟨r, hr, hc.byte hb⟩
  have K : Keep [.r3, .r4, .r5, .r6] s u := by
    refine ⟨fun r hr => ?_, by rw [kp.2.1, K₁.2.1], by rw [kp.2.2, K₁.2.2]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [kp.1 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]), K₁.1 r (by simp [hr.1, hr.2.1, hr.2.2.1])]
  refine k σ s u hs ?_ K (by rw [b, m₁])
  refine h₀.of_scrs (os := [(dst, n)]) K (sp.trans sp₁) (fun p hp => by
      simp only [List.mem_singleton] at hp; subst hp; exact ⟨dE, by simpa using dK, by simpa using dS⟩)
    (by rw [← m₁]; exact f.mono fun r hr => by simp at hr ⊢; exact .inl hr) fun x hx => .inl ?_
  obtain ⟨hm, ha⟩ := List.mem_filter.mp hx
  exact ⟨hm, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; simpa using ha⟩

end

end VG.Proof.Dsa.PPC64LE.Gen

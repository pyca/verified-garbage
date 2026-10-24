module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Frame
public import VerifiedGarbage.Proof.Rsa.KeyArrays
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

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
    omega
  · have : wB 256 + 8 * wWords 256 ≤ 8 * (64 * 256 + 1024) := by decide
    omega
  · have : wB 384 + 8 * wWords 384 ≤ 8 * (64 * 384 + 1024) := by decide
    omega

theorem GI.kBig (h : GI G STK σ V LS s) : kB G.pLen + kz G.pLen ≤ wB G.pLen := by
  rcases h.lens3 with e | e | e <;> rw [e] <;> decide

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

theorem w32_frame {B : Addr} {Z : Nat} {m m' : Mem} {rs : List Region} (f : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨B, Z⟩ : Region).Disjoint r) (hZ : Z ≤ 2 ^ 64) {d : Nat} (h : d + 4 ≤ Z) :
    w32 m' B d = w32 m B d := by
  simp only [w32]
  rw [f.readW (r := ⟨B, Z⟩) (Offset.contains_base _ h (by omega)) hd (by decide)]

theorem kz_eq {L : Nat} (hL : L = 128 ∨ L = 256 ∨ L = 384) : kz L ≤ 2 ^ 64 := by
  rcases hL with rfl | rfl | rfl <;> decide

/-- The arrays fit the key working space. -/
theorem arrs_fit {L j : Nat} (hL : L = 128 ∨ L = 256 ∨ L = 384) (hj : j < nArrs) :
    arr (L / 4) j + 4 * (L / 4 + 2) ≤ kz L := by
  have := arr_end (w := L / 4) hj
  simp only [arr, S, hdr, nArrs, kz] at *
  rcases hL with rfl | rfl | rfl <;> omega

theorem num_frame {B : Addr} {L : Nat} (hL : L = 128 ∨ L = 256 ∨ L = 384) {m m' : Mem}
    {rs : List Region} (f : Frame rs m m') (hd : ∀ r ∈ rs, (⟨B, kz L⟩ : Region).Disjoint r)
    {j : Nat} (hj : j < nArrs) : num m' B (L / 4) j = num m B (L / 4) j := by
  have := arrs_fit hL hj
  exact val32_congr fun i hi => w32_frame f hd (kz_eq hL) (by omega)

theorem slot_frame {B : Addr} {L : Nat} (hL : L = 128 ∨ L = 256 ∨ L = 384) {m m' : Mem}
    {rs : List Region} (f : Frame rs m m') (hd : ∀ r ∈ rs, (⟨B, kz L⟩ : Region).Disjoint r)
    {d : Nat} (hdk : KlsOk d) : slot m' B d = slot m B d :=
  w32_frame f hd (kz_eq hL) (by obtain ⟨h1, _⟩ := hdk; simp only [kz, hdr] at h1 ⊢; omega)

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
    · exact gi.scr_below (by omega)
  -- The header: a step past it.
  have gi' : GI G STK σ c.V c.LS t := by
    have hd : ∀ q, q + 8 ≤ hEnd → ∀ r' ∈ G.rss os ++ [rBelow σ STK], (G.rs q 8).Disjoint r' := fun q hq r' hr' => by
      rcases mem r' hr' with ⟨p, hp, rfl⟩ | rfl
      · obtain ⟨a, _, b⟩ := hon' p hp; exact gi.sdisj (.inl (by omega)) (by omega) b
      · exact gi.scr_below (by omega)
    refine ⟨gi.pre, gi.hG, sp.trans gi.sp, r.2.1.trans gi.rd, r.2.2.trans gi.wr, (r.gpr h28).trans gi.r28,
      fun i hi => ?_, ?_, fun p hp => ?_, fun p hp => ?_, gi.ls, gi.frame.trans (f.sub fun x hx => ?_)⟩
    · rw [fw_frame f (hd _ (by simp only [hEnd]; omega))]; exact gi.saved i hi
    · rw [fw_frame f (hd _ (by decide))]; exact gi.lr
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
  · rw [slot_frame h.lens f kd (h.kslOk d hd)]; exact h.ksl d hd

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
    (gi₀.kdisj (o := o) (n := 8) (.inl (by simp only [kB, fSave] at oS ⊢; omega))
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
  · rw [slot_frame h.lens f (fun r' hr' => by simp only [List.mem_singleton] at hr'; subst hr'; exact hd.symm)
      (h.kslOk d hd')]
    exact h.ksl d hd'

end

end VG.Proof.Dsa.PPC64LE.Gen

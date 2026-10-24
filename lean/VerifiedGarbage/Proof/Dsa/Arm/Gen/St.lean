module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Steps
public import VerifiedGarbage.Proof.Rsa.Arm.KeyArrs
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on ARMv7: a state of the search

`SS G σ c s`: a state of the search (`GI`), with the key working space's
registers (`r7`–`r9`, kept from `ksRegs` on), the bytes the claims `c.cl` of
`scratch` hold, below the key working space, and the arrays and header
words of the key working space that `c` lists.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.Proof.Rsa.Arm.Keys
open VG.Impl.Dsa.Arm.Generation
open VG.Impl.Rsa.Arm.Keys (hdr)
open VG.Proof.Mont (w32 val32 val32_congr)
open VG.Proof.X25519.Arm (Rest Upd Mupd)

/-- Claims on `scratch`: the bytes at an offset. -/
abbrev Claims := List (Nat × List Byte)

namespace GP
variable (G : GP)

/-- Byte `o` of `scratch`. -/
abbrev sa (o : Nat) : Addr := State.addr G.scr + BitVec.ofNat 64 o
/-- The `n` bytes at byte `o` of `scratch`. -/
abbrev rs (o n : Nat) : Region := ⟨G.sa o, n⟩
/-- The key working space. -/
abbrev KB : BitVec 32 := G.scr + BitVec.ofNat 32 (sK G.pLen)
abbrev w : Nat := G.pLen / 4
abbrev rK : Region := ⟨State.addr G.KB, kz G.pLen⟩

end GP

/-- The claims hold. -/
def SB (G : GP) (m : Mem) (cl : Claims) : Prop :=
  ∀ x ∈ cl, Spec.Rsa.bytesAt m (G.sa x.1) x.2.length = x.2

/-- What a stage keeps: frame words, claims, arrays and header words. -/
structure Cfg where
  V : Nat → BitVec 32 := fun _ => 0
  LS : List Nat := []
  cl : Claims := []
  A : Nat → Nat := fun _ => 0
  live : List Nat := []
  KV : Nat → Nat := fun _ => 0
  kls : List Nat := []

/-- A header word a stage keeps. -/
abbrev KlsOk (d : Nat) : Prop := d + 4 ≤ hdr ∧ d % 4 = 0

structure SS (G : GP) (σ : State) (c : Cfg) (s : State) : Prop where
  gi : GI G σ c.V c.LS s
  r7 : s.gpr .r7 = BitVec.ofNat 32 (S G.w)
  r8 : s.gpr .r8 = G.KB
  r9 : s.gpr .r9 = BitVec.ofNat 32 G.w
  sb : SB G s.mem c.cl
  clOk : ∀ x ∈ c.cl, x.1 + x.2.length ≤ sK G.pLen
  arrs : Arrs s.mem G.KB G.w c.A c.live
  liveOk : ∀ j ∈ c.live, j < nArrs
  ksl : ∀ d ∈ c.kls, slot s.mem G.KB d = c.KV d
  kslOk : ∀ d ∈ c.kls, KlsOk d

/-! ## Sizes -/

theorem CIn.lens' {σ : State} (h : CIn σ) :
    ((mkG σ).pLen = 128 ∧ (mkG σ).qLen = 20) ∨ ((mkG σ).pLen = 256 ∧ (mkG σ).qLen = 32) ∨
      ((mkG σ).pLen = 384 ∧ (mkG σ).qLen = 32) := h.lens

section
variable {G : GP} {σ : State} {V : Nat → BitVec 32} {LS : List Nat} {s : State}

theorem GI.lens (h : GI G σ V LS s) :
    (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32) := by
  rw [← h.hG]; exact h.pre.lens

/-- `scratch` holds the key working space and everything below it. -/
theorem GI.scrBig (h : GI G σ V LS s) : sK G.pLen + kz G.pLen ≤ G.scrLen * 8 := by
  have l := h.lens
  have := h.pre.scrLen
  have e1 : (σ.gpr .r2).toNat = G.pLen := by rw [← h.hG]; rfl
  have e2 : (stackArg σ 7).toNat = G.scrLen := by rw [← h.hG]; rfl
  rw [e1, e2] at this
  simp only [Spec.Dsa.generationScratchWords] at this
  simp only [sK, sA, wa, kz]
  generalize G.pLen = L at *; generalize G.scrLen = n at *
  clear e1 e2
  rcases l with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega

theorem GI.scrFit (h : GI G σ V LS s) : G.scr.toNat + G.scrLen * 8 ≤ 2 ^ 32 := by
  have := h.pre.nC; rw [← h.hG]; exact this

/-- Byte `o` of `scratch`, from a pointer. -/
theorem GI.saddr (h : GI G σ V LS s) {o : Nat} (ho : o < G.scrLen * 8) :
    State.addr (G.scr + BitVec.ofNat 32 o) = G.sa o := by
  have := h.scrFit; exact addr_add (by omega)

theorem GI.kaddr (h : GI G σ V LS s) : State.addr G.KB = G.sa (sK G.pLen) := by
  have := h.scrBig; have : 0 < kz G.pLen := by simp only [kz]; omega
  exact h.saddr (by omega)

/-- A range of `scratch` is writable. -/
theorem sw (G : GP) {o n : Nat} (ho : o + n ≤ G.scrLen * 8) :
    Region.Sub (G.rs o n) G.rScr :=
  Offset.sub_base _ ho

theorem GI.inScr (h : GI G σ V LS s) {o n : Nat} (ho : o + n ≤ G.scrLen * 8) :
    InRegions s.wr (G.sa o) n := by
  have := h.scrFit
  refine ⟨G.rScr, ?_, Offset.contains_base _ ho (by omega)⟩
  rw [h.wr, h.pre.wr, h.hG]; simp

theorem GI.kSub (h : GI G σ V LS s) : Region.Sub G.rK G.rScr := by
  show Region.Sub ⟨State.addr G.KB, _⟩ _
  rw [h.kaddr]; exact sw G h.scrBig

/-- Ranges of `scratch` apart by their offsets are disjoint. -/
theorem GI.sdisj (h : GI G σ V LS s) {o n o' n' : Nat} (hs : o + n ≤ o' ∨ o' + n' ≤ o)
    (h1 : o + n ≤ G.scrLen * 8) (h2 : o' + n' ≤ G.scrLen * 8) :
    (G.rs o n).Disjoint (G.rs o' n') := by
  have := h.scrFit
  exact Offset.disjoint _ hs (by omega) (by omega)

/-- `scratch` is apart from the frame and the stack below it. -/
theorem GI.scr_frame (h : GI G σ V LS s) {o n : Nat} (ho : o + n ≤ G.scrLen * 8) :
    (G.rs o n).Disjoint G.rFrame :=
  h.frame_scr.symm.sub_left (sw G ho)

theorem GI.scr_below (h : GI G σ V LS s) {o n : Nat} (ho : o + n ≤ G.scrLen * 8) :
    (G.rs o n).Disjoint G.rBelow := by
  have := h.pre.fC; rw [h.hG] at this
  exact (this.symm.sub_left (sw G ho)).sub_right h.belowSub

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

/-- The arrays fit the key working space. -/
theorem arrs_fit {L j : Nat} (hL : L = 128 ∨ L = 256 ∨ L = 384) (hj : j < nArrs) :
    arr (L / 4) j + 4 * (L / 4 + 2) ≤ kz L := by
  have := arr_end (w := L / 4) hj
  simp only [arr, S, hdr, nArrs, kz] at *
  rcases hL with rfl | rfl | rfl <;> omega

theorem w32_frame {B : Addr} {Z : Nat} {m m' : Mem} {rs : List Region} (f : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨B, Z⟩ : Region).Disjoint r) (hZ : Z ≤ 2 ^ 64) {d : Nat} (h : d + 4 ≤ Z) :
    w32 m' B d = w32 m B d := by
  simp only [w32]
  rw [f.readW (r := ⟨B, Z⟩) (Offset.contains_base _ h (by omega)) hd (by decide)]

theorem num_frame {B : BitVec 32} {L : Nat} (hL : L = 128 ∨ L = 256 ∨ L = 384) {m m' : Mem}
    {rs : List Region} (f : Frame rs m m') (hd : ∀ r ∈ rs, (⟨State.addr B, kz L⟩ : Region).Disjoint r)
    {j : Nat} (hj : j < nArrs) : num m' B (L / 4) j = num m B (L / 4) j := by
  have := arrs_fit hL hj
  exact val32_congr fun i hi => w32_frame f hd (by simp only [kz]; rcases hL with rfl | rfl | rfl <;> decide)
    (by omega)

theorem slot_frame {B : BitVec 32} {L : Nat} (hL : L = 128 ∨ L = 256 ∨ L = 384) {m m' : Mem}
    {rs : List Region} (f : Frame rs m m') (hd : ∀ r ∈ rs, (⟨State.addr B, kz L⟩ : Region).Disjoint r)
    {d : Nat} (hdk : KlsOk d) : slot m' B d = slot m B d :=
  w32_frame f hd (by simp only [kz]; rcases hL with rfl | rfl | rfl <;> decide)
    (by obtain ⟨h1, _⟩ := hdk; simp only [kz, hdr] at h1 ⊢; omega)

/-! ## Steps that keep a state of the search -/

section
variable {G : GP} {σ : State} {c : Cfg} {s t : State}

theorem SS.lens (h : SS G σ c s) : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384 := by
  rcases h.gi.lens with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> simp [e]

/-- Registers alone change, the key working space's kept. -/
theorem SS.of_rest {ws : List Reg} (h : SS G σ c s) (r : Rest ws s t) (m : t.mem = s.mem)
    (h7 : .r7 ∉ ws := by decide) (h8 : .r8 ∉ ws := by decide) (h9 : .r9 ∉ ws := by decide) : SS G σ c t :=
  ⟨h.gi.of_rest r m, (r.gpr _ h7).trans h.r7, (r.gpr _ h8).trans h.r8, (r.gpr _ h9).trans h.r9,
    m ▸ h.sb, h.clOk, m ▸ h.arrs, h.liveOk, m ▸ h.ksl, h.kslOk⟩

/-- Fewer frame words, claims, arrays or header words. -/
theorem SS.mono (h : SS G σ c s) {c' : Cfg} (hV : ∀ o ∈ c'.LS, o ∈ c.LS ∧ c.V o = c'.V o)
    (hcl : ∀ x ∈ c'.cl, x ∈ c.cl) (hA : ∀ j ∈ c'.live, j ∈ c.live ∧ c.A j = c'.A j)
    (hK : ∀ d ∈ c'.kls, d ∈ c.kls ∧ c.KV d = c'.KV d) : SS G σ c' s := by
  obtain ⟨gi, r7, r8, r9, sb, clOk, arrs, liveOk, ksl, kslOk⟩ := h
  refine ⟨⟨gi.pre, gi.hG, gi.sp, gi.rd, gi.wr, gi.saved, gi.fixed, fun o ho => ?_, fun o ho => gi.ls o (hV o ho).1,
    gi.frame⟩, r7, r8, r9, sb.sub hcl, fun x hx => clOk x (hcl x hx), fun j hj => ?_,
    fun j hj => liveOk j (hA j hj).1, fun d hd => ?_, fun d hd => kslOk d (hK d hd).1⟩
  · rw [← (hV o ho).2]; exact gi.slots o (hV o ho).1
  · rw [← (hA j hj).2]; exact arrs j (hA j hj).1
  · rw [← (hK d hd).2]; exact ksl d (hK d hd).1

/-- The ranges `(o, n)` of `scratch`. -/
abbrev GP.rss (G : GP) (os : List (Nat × Nat)) : List Region := os.map fun p => G.rs p.1 p.2

/-- A step that writes the ranges `os` of `scratch`, below the key working
space, and the stack below the frame: the claims `cl'`, each kept and apart
from the ranges, or holding. -/
theorem SS.of_scrs {ws : List Reg} (h : SS G σ c s) (r : Rest ws s t) {os : List (Nat × Nat)}
    (hon : ∀ p ∈ os, p.1 + p.2 ≤ sK G.pLen)
    (f : Frame (G.rss os ++ [G.rBelow]) s.mem t.mem) {cl' : Claims}
    (hcl : ∀ x ∈ cl', (x ∈ c.cl ∧ ∀ p ∈ os, Apart p.1 p.2 x) ∨
      (Spec.Rsa.bytesAt t.mem (G.sa x.1) x.2.length = x.2 ∧ x.1 + x.2.length ≤ sK G.pLen))
    (h7 : .r7 ∉ ws := by decide) (h8 : .r8 ∉ ws := by decide) (h9 : .r9 ∉ ws := by decide) :
    SS G σ { c with cl := cl' } t := by
  have gi := h.gi
  have big := gi.scrBig
  have fit := gi.scrFit
  have kz0 : 0 < kz G.pLen := by simp only [kz]; omega
  have mem : ∀ r' ∈ G.rss os ++ [G.rBelow], (∃ p ∈ os, r' = G.rs p.1 p.2) ∨ r' = G.rBelow := fun r' hr' => by
    simp only [GP.rss, List.mem_append, List.mem_map, List.mem_singleton] at hr'
    rcases hr' with ⟨p, hp, rfl⟩ | rfl
    · exact .inl ⟨p, hp, rfl⟩
    · exact .inr rfl
  have fs : Frame [G.rScr, G.rBelow] s.mem t.mem := f.sub fun x hx => by
    rcases mem x hx with ⟨p, hp, rfl⟩ | rfl
    · exact ⟨G.rScr, List.mem_cons_self, sw G (by have := hon p hp; omega)⟩
    · exact ⟨G.rBelow, by simp, fun _ h => h⟩
  -- The key working space is apart from what the step writes.
  have kd : ∀ r' ∈ G.rss os ++ [G.rBelow], G.rK.Disjoint r' := fun r' hr' => by
    show Region.Disjoint ⟨State.addr G.KB, _⟩ _
    rw [gi.kaddr]
    rcases mem r' hr' with ⟨p, hp, rfl⟩ | rfl
    · exact gi.sdisj (.inr (hon p hp)) big (by have := hon p hp; omega)
    · exact gi.scr_below big
  refine ⟨gi.of_scr r fs, (r.gpr _ h7).trans h.r7, (r.gpr _ h8).trans h.r8, (r.gpr _ h9).trans h.r9,
    fun x hx => ?_, fun x hx => ?_, fun j hj => ?_, h.liveOk, fun d hd => ?_, h.kslOk⟩
  · rcases hcl x hx with ⟨hm, ha⟩ | ⟨e, _⟩
    · have := h.clOk x hm
      rw [VG.Proof.Dsa.Generation.frame_bytesAt f (fun r' hr' => by
        rcases mem r' hr' with ⟨p, hp, rfl⟩ | rfl
        · exact gi.sdisj (ha p hp) (by omega) (by have := hon p hp; omega)
        · exact gi.scr_below (by omega)) (by omega)]
      exact h.sb x hm
    · exact e
  · rcases hcl x hx with ⟨hm, _⟩ | ⟨_, b⟩
    · exact h.clOk x hm
    · exact b
  · rw [num_frame h.lens f kd (h.liveOk j hj)]; exact h.arrs j hj
  · rw [slot_frame h.lens f kd (h.kslOk d hd)]; exact h.ksl d hd

/-- A step that writes the range `[o, o + n)` of `scratch`. -/
theorem SS.of_scr {ws : List Reg} (h : SS G σ c s) (r : Rest ws s t) {o n : Nat} (hon : o + n ≤ sK G.pLen)
    (f : Frame [G.rs o n, G.rBelow] s.mem t.mem) {cl' : Claims}
    (hcl : ∀ x ∈ cl', (x ∈ c.cl ∧ Apart o n x) ∨
      (Spec.Rsa.bytesAt t.mem (G.sa x.1) x.2.length = x.2 ∧ x.1 + x.2.length ≤ sK G.pLen))
    (h7 : .r7 ∉ ws := by decide) (h8 : .r8 ∉ ws := by decide) (h9 : .r9 ∉ ws := by decide) :
    SS G σ { c with cl := cl' } t :=
  h.of_scrs (os := [(o, n)]) r (by simpa using hon) f
    (fun x hx => (hcl x hx).imp (fun ⟨hm, ha⟩ => ⟨hm, by simpa using ha⟩) id) h7 h8 h9

end

end VG.Proof.Dsa.Arm.Gen

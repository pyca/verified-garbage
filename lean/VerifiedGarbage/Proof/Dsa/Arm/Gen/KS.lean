module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Frame
public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps
public import VerifiedGarbage.Proof.Rsa.Arm.KeyBits
public import VerifiedGarbage.Proof.Rsa.Arm.KeyWord
public import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # DSA parameter generation on ARMv7: steps in the key working space

The operations on the arrays of the key working space
(`Impl/Rsa/Arm/KeyWs.lean`) are proven (`Proof/Rsa/Arm/KeyOps.lean`, …) on a
state whose one writable region is the working space (`Ws`). `SS.ksWP` runs
such code from a state of the search, narrowed to the working space
(`SS.ws`), and `SS.of_ks` is the state after it: what the step wrote of
the arrays and header words, everything else as it was.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.Proof.Mont VG.Proof.Rsa.Arm.Keys
open VG.Impl.Dsa.Arm.Generation
open VG.Impl.Rsa.Arm.Keys (hdr)
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Rsa.Arm.Recover (VP)

section
variable {G : GP} {σ : State} {c : Cfg} {s : State}

/-- The state narrowed to the key working space. -/
abbrev GP.ksState (G : GP) (s : State) : State := s.withRegions s.rd [G.rK]

theorem SS.kbNat (h : SS G σ c s) : G.KB.toNat = G.scr.toNat + sK G.pLen := by
  have := h.gi.scrBig; have := h.gi.scrFit
  have : 0 < kz G.pLen := by simp only [kz]; omega
  rw [GP.KB, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show sK G.pLen < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem SS.wsWith (h : SS G σ c s) (rd : List Region) : Ws (s.withRegions rd [G.rK]) G.KB (kz G.pLen) G.w nArrs := by
  have := h.gi.scrBig; have := h.gi.scrFit
  have e := h.kbNat
  have l := h.lens
  refine ⟨by omega, List.mem_singleton_self _, ?_, ?_, ?_, h.r7, h.r8, h.r9⟩ <;>
    simp only [arr, S, hdr, nArrs, kz, GP.w] <;> rcases l with e | e | e <;> rw [e] <;> decide

theorem SS.ws (h : SS G σ c s) : Ws (G.ksState s) G.KB (kz G.pLen) G.w nArrs := h.wsWith s.rd

/-- The narrowed state's regions are within the state's. -/
theorem SS.kcov (h : SS G σ c s) : Covers (s.rd ++ [G.rK]) (s.rd ++ s.wr) ∧ Covers [G.rK] s.wr := by
  have big := h.gi.scrBig
  have inS : G.rScr ∈ s.wr := by rw [h.gi.wr, h.gi.pre.wr, h.gi.hG]; simp
  have hw : Covers [G.rK] s.wr := (Covers.of_sub (rs' := [G.rScr]) fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨G.rScr, List.mem_singleton_self _, sK G.pLen, h.gi.kaddr, by omega⟩).trans
    (Covers.of_mem fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact inS)
  exact ⟨Covers.append (Covers.refl _) hw, hw⟩

/-- Code in the key working space alone, from a state of the search. -/
theorem SS.ksWP (h : SS G σ c s) {code : Prog isa} (hn : code.noCalls = true) {P : State → Prop}
    (hwp : WP isa code (G.ksState s) P) {Q : State → Prop}
    (k : ∀ t, P (G.ksState t) → t.rd = s.rd → t.wr = s.wr → Frame [G.rK] s.mem t.mem → Q t) :
    WP isa code s Q := by
  refine regionModel.wp_narrow (r := s.rd) (w := [G.rK]) hwp h.kcov.1 h.kcov.2
    (Code.noFrames_of_noCalls hn) (.inl hn) fun t s' _ hr hw' f p => ?_
  have hr' : s'.rd = s.rd := hr
  refine k s' ?_ hr' hw' f
  show P (s'.withRegions s'.rd _)
  rw [hr']; exact p

/-- Code in the key working space, also reading the regions `rs`. -/
theorem SS.ksWPr (h : SS G σ c s) {rs : List Region} (hrs : Covers rs s.wr) {code : Prog isa}
    (hn : code.noCalls = true) {P : State → Prop} (hwp : WP isa code (s.withRegions (s.rd ++ rs) [G.rK]) P)
    {Q : State → Prop}
    (k : ∀ t, P (t.withRegions (s.rd ++ rs) [G.rK]) → t.rd = s.rd → t.wr = s.wr → Frame [G.rK] s.mem t.mem →
      Q t) :
    WP isa code s Q :=
  regionModel.wp_narrow (r := s.rd ++ rs) (w := [G.rK]) hwp
    (Covers.append_left (Covers.append (Covers.refl _) hrs) h.kcov.2.right) h.kcov.2
    (Code.noFrames_of_noCalls hn) (.inl hn) fun _ s' _ hr hw' f p => k s' p hr hw' f

/-- After a step in the key working space: its arrays and header words, and
the working space's registers. -/
theorem SS.of_ks' (h : SS G σ c s) {t : State} {ws : List Reg} (r : Rest ws s t)
    (f : Frame [G.rK] s.mem t.mem) {A : Nat → Nat} {live : List Nat} {KV : Nat → Nat} {kls : List Nat}
    (ha : Arrs t.mem G.KB G.w A live) (hl : ∀ j ∈ live, j < nArrs)
    (hk : ∀ d ∈ kls, slot t.mem G.KB d = KV d) (hko : ∀ d ∈ kls, KlsOk d)
    (e7 : t.gpr .r7 = BitVec.ofNat 32 (S G.w)) (e8 : t.gpr .r8 = G.KB) (e9 : t.gpr .r9 = BitVec.ofNat 32 G.w) :
    SS G σ { c with A := A, live := live, KV := KV, kls := kls } t := by
  have gi := h.gi
  have big := gi.scrBig
  have fit := gi.scrFit
  have kz0 : 0 < kz G.pLen := by simp only [kz]; omega
  have kd : ∀ x ∈ c.cl, ∀ r ∈ [G.rK], (G.rs x.1 x.2.length).Disjoint r := fun x hx r hr => by
    rw [List.mem_singleton] at hr; subst hr
    show Region.Disjoint _ ⟨State.addr G.KB, _⟩
    rw [gi.kaddr]
    have := h.clOk x hx
    exact gi.sdisj (.inl this) (by omega) big
  refine ⟨gi.of_scr r (f.sub fun x hx => ?_), e7, e8, e9, h.sb.frame f kd fun x hx => ?_, h.clOk, ha, hl, hk, hko⟩
  · rw [List.mem_singleton] at hx; subst hx; exact ⟨G.rScr, List.mem_cons_self, gi.kSub⟩
  · have := h.clOk x hx; omega

/-- After a step in the key working space: its arrays and header words. -/
theorem SS.of_ks (h : SS G σ c s) {t : State} {ws : List Reg} (r : Rest ws s t)
    (f : Frame [G.rK] s.mem t.mem) {A : Nat → Nat} {live : List Nat} {KV : Nat → Nat} {kls : List Nat}
    (ha : Arrs t.mem G.KB G.w A live) (hl : ∀ j ∈ live, j < nArrs)
    (hk : ∀ d ∈ kls, slot t.mem G.KB d = KV d) (hko : ∀ d ∈ kls, KlsOk d)
    (h7 : .r7 ∉ ws := by decide) (h8 : .r8 ∉ ws := by decide) (h9 : .r9 ∉ ws := by decide) :
    SS G σ { c with A := A, live := live, KV := KV, kls := kls } t :=
  h.of_ks' r f ha hl hk hko ((r.gpr _ h7).trans h.r7) ((r.gpr _ h8).trans h.r8) ((r.gpr _ h9).trans h.r9)

/-- An operation on the key working space (`Ws` to `Ws`, writing the arrays
`js` and header words `ds`), from a state of the search. -/
theorem SS.ksOp (h : SS G σ c s) {code : Prog isa} (hn : code.noCalls = true) {js ds : List Nat}
    {P : State → Prop} {ws : List Reg}
    (hwp : WP isa code (G.ksState s) fun t => Ws t G.KB (kz G.pLen) G.w nArrs ∧
      Keep G.KB G.w js ds s.mem t.mem ∧ P t ∧ Rest ws (G.ksState s) t) {Q : State → Prop}
    (k : ∀ t, Keep G.KB G.w js ds s.mem t.mem → P (G.ksState t) → Rest ws s t → Frame [G.rK] s.mem t.mem → Q t) :
    WP isa code s Q :=
  h.ksWP hn hwp fun t ⟨_, kp, p, r⟩ hr hw f => k t kp p ⟨r.gpr, hr, hw, r.sp⟩ f

/-- After an operation that writes the array `o` (to `v`) and no header word. -/
theorem SS.of_op (h : SS G σ c s) {t : State} {ws : List Reg} (r : Rest ws s t) (f : Frame [G.rK] s.mem t.mem)
    {o v : Nat} (ho : o < nArrs) (kp : Keep G.KB G.w [o] [] s.mem t.mem) (e : num t.mem G.KB G.w o = v)
    (h7 : .r7 ∉ ws := by decide) (h8 : .r8 ∉ ws := by decide) (h9 : .r9 ∉ ws := by decide) :
    SS G σ { c with A := VG.Proof.Rsa.Arm.Keys.upd c.A o v, live := o :: c.live } t := by
  have hw := h.ws
  have a := (h.arrs.write kp hw e (fun j hj => by
    by_cases hjo : j = o
    · exact .inl hjo
    · exact .inr ⟨h.liveOk j hj, by simpa using hjo⟩) (by simp)).cons (o := o) (by rw [VG.Proof.Rsa.Arm.Keys.upd_self]; exact e)
  refine h.of_ks r f a (fun j hj => ?_) (fun d hd => ?_) h.kslOk h7 h8 h9
  · rcases List.mem_cons.mp hj with rfl | hj
    · exact ho
    · exact h.liveOk j hj
  · rw [kp.slot (h.kslOk d hd).1 (by simp)]; exact h.ksl d hd

/-- After an operation that writes the header word `d` (to `v`) and no array. -/
theorem SS.of_opS (h : SS G σ c s) {t : State} {ws : List Reg} (r : Rest ws s t) (f : Frame [G.rK] s.mem t.mem)
    {d v : Nat} (hd : KlsOk d) (kp : Keep G.KB G.w [] [d] s.mem t.mem) (e : slot t.mem G.KB d = v)
    (h7 : .r7 ∉ ws := by decide) (h8 : .r8 ∉ ws := by decide) (h9 : .r9 ∉ ws := by decide) :
    SS G σ { c with KV := VG.Proof.Rsa.Arm.Keys.upd c.KV d v, kls := d :: c.kls } t := by
  have hw := h.ws
  refine h.of_ks r f (h.arrs.keep kp hw (fun j hj => ⟨h.liveOk j hj, by simp⟩) (by simpa using hd.1))
    h.liveOk (fun e' he => ?_) (fun e' he => ?_) h7 h8 h9
  · by_cases hed : e' = d
    · subst hed; rw [VG.Proof.Rsa.Arm.Keys.upd_self]; exact e
    · rcases List.mem_cons.mp he with rfl | he
      · exact absurd rfl hed
      rw [VG.Proof.Rsa.Arm.Keys.upd_ne _ _ hed, kp.slot (h.kslOk e' he).1 (by
        simp only [List.mem_singleton, forall_eq]
        have := h.kslOk e' he; have := hd; simp only [KlsOk] at *; omega)]
      exact h.ksl e' he
  · rcases List.mem_cons.mp he with rfl | he
    · exact hd
    · exact h.kslOk e' he

end

end VG.Proof.Dsa.Arm.Gen

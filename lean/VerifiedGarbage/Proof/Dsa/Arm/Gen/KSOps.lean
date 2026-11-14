module

import VerifiedGarbage.Proof.Dsa.Arm.Gen.Frame
public import VerifiedGarbage.Proof.Rsa.Arm.KeyBits
public import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.St
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Rsa.Arm.KeyWs
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Test
import VerifiedGarbage.Proof.Rsa.Arm.KeyWord
import VerifiedGarbage.Proof.Dsa.Arm.Gen.CT
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.VP

/-! ### `Dsa.Arm.Gen.KS`, which only this module used -/

section

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
  have : 0 < kz G.pLen := by simp only [kz]; omega_using []
  rw [GP.KB, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show sK G.pLen < 2 ^ 32 by omega_arith),
    Nat.mod_eq_of_lt (by omega_arith)]

theorem SS.wsWith (h : SS G σ c s) (rd : List Region) : Ws (s.withRegions rd [G.rK]) G.KB (kz G.pLen) G.w nArrs := by
  have := h.gi.scrBig; have := h.gi.scrFit
  have e := h.kbNat
  have l := h.lens
  refine ⟨by omega_arith, List.mem_singleton_self _, ?_, ?_, ?_, h.r7, h.r8, h.r9⟩ <;>
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
theorem SS.ksWPr (h : SS G σ c s) {rs : List Region} (hrs : Covers rs (s.rd ++ s.wr)) {code : Prog isa}
    (hn : code.noCalls = true) {P : State → Prop} (hwp : WP isa code (s.withRegions (s.rd ++ rs) [G.rK]) P)
    {Q : State → Prop}
    (k : ∀ t, P (t.withRegions (s.rd ++ rs) [G.rK]) → t.rd = s.rd → t.wr = s.wr → Frame [G.rK] s.mem t.mem →
      Q t) :
    WP isa code s Q :=
  regionModel.wp_narrow (r := s.rd ++ rs) (w := [G.rK]) hwp
    (Covers.append_left (Covers.append_left (Covers.left (Covers.refl _)) hrs) h.kcov.2.right) h.kcov.2
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
  have kz0 : 0 < kz G.pLen := by simp only [kz]; omega_using []
  have kd : ∀ x ∈ c.cl, ∀ r ∈ [G.rK], (G.rs x.1 x.2.length).Disjoint r := fun x hx r hr => by
    rw [List.mem_singleton] at hr; subst hr
    show Region.Disjoint _ ⟨State.addr G.KB, _⟩
    rw [gi.kaddr]
    have := h.clOk x hx
    exact gi.sdisj (.inl this) (by omega_using [big, this]) big
  refine ⟨gi.of_scr r (f.sub fun x hx => ?_), e7, e8, e9, h.sb.frame f kd fun x hx => ?_, h.clOk, ha, hl, hk, hko⟩
  · rw [List.mem_singleton] at hx; subst hx; exact ⟨G.rScr, List.mem_cons_self, gi.kSub⟩
  · have := h.clOk x hx; omega_using [big, fit, this]

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
        have := h.kslOk e' he; have := hd; simp only [KlsOk] at *; omega_arith)]
      exact h.ksl e' he
  · rcases List.mem_cons.mp he with rfl | he
    · exact hd
    · exact h.kslOk e' he

end

end VG.Proof.Dsa.Arm.Gen

end

end


/-! # DSA parameter generation on ARMv7: the operations on the arrays as pieces

Each operation of the key working space from one stage (`St`) to the next,
with what it writes recorded in the stage's arrays (`A`, `live`) or header
words (`KV`, `kls`). The taint analysis checks each with the key working
space's registers (`r7`–`r9`) public, which both runs agree on.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.Proof.Mont VG.Proof.Rsa.Arm.Keys
open VG.Impl.Dsa.Arm.Generation
open VG.Impl.Rsa.Arm.Keys (hdr sub3 sel copy bitOf orOne clrLow ptr)
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Rsa.Arm.Recover (VP)

/-- A taint certificate with the key working space's registers public. -/
abbrev Cert7 (code : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r7, .r8, .r9]) code hc).isSome = true

/-- Shorthand for the arrays' updates. -/
abbrev KU (A : Nat → Nat) (j v : Nat) : Nat → Nat := VG.Proof.Rsa.Arm.Keys.upd A j v

section
variable {G : GP} {c : Cfg} {X : State → Prop}

theorem ks_vp {F Q : State → State → Prop} {cf : State → Cfg} {code : Prog isa} (cert : Cert7 code)
    (hF : ∀ σ s, F σ s → SS G σ (cf σ) s) (wp : ∀ σ s, F σ s → WP isa code s (Q σ)) : VP F code Q :=
  VP.taint _ cert (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
    have a := hF _ _ h₁; have b := hF _ _ h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [a.r7, b.r7]
    · rw [a.r8, b.r8]
    · rw [a.r9, b.r9]) wp

/-- `[o] := [a] − [b]`, for `[b] ≤ [a]`. -/
theorem sub3_vp {o a b : Nat} (cert : Cert7 (sub3 o a b)) (ho : o < nArrs) (ha : a ∈ c.live) (hb : b ∈ c.live)
    (hoa : o ≠ a) (hob : o ≠ b) (hle : c.A b ≤ c.A a) :
    VP (St G c X) (sub3 o a b) (St G { c with A := KU c.A o (c.A a - c.A b), live := o :: c.live } X) := by
  refine ks_vp cert (fun σ s h => h.1) fun σ s ⟨h, x⟩ => ?_
  have hw := h.ws
  have ha' : a < nArrs := h.liveOk a ha
  have hb' : b < nArrs := h.liveOk b hb
  have va := h.arrs.get ha
  have vb := h.arrs.get hb
  refine h.ksOp (P := fun t => num t.mem G.KB G.w o + num s.mem G.KB G.w b =
      num s.mem G.KB G.w a + 2 ^ (32 * G.w) * (t.gpr .r11).toNat ∧ (t.gpr .r11).toNat ≤ 1) rfl
    ((sub3_ok hw ho ha' hb' (by decide) hoa hob).mono fun t ⟨w, k, v, br, r⟩ => ⟨w, k, ⟨v, br⟩, r⟩)
    fun t k ⟨v, br⟩ R f => ⟨h.of_op R f ho k ?_, x⟩
  simp only [GP.ksState, State.withRegions_mem, State.withRegions_gpr] at v br
  rw [va, vb] at v
  have lt : num t.mem G.KB G.w o < 2 ^ (32 * G.w) := val32_lt _ _ _ _
  have alt : c.A a < 2 ^ (32 * G.w) := va ▸ val32_lt _ _ _ _
  generalize 2 ^ (32 * G.w) = M at v lt alt
  rcases (by omega_using [br] : (t.gpr .r11).toNat = 0 ∨ (t.gpr .r11).toNat = 1) with e | e <;> rw [e] at v
  · omega_using [v]
  · have : M * 1 = M := Nat.mul_one M
    omega_using [hle, v, lt]

/-- `[o] := [b]` if the header word `sl` is 1, else `[a]`. -/
theorem sel_vp {o a b sl : Nat} (cert : Cert7 (sel o a b sl)) (ho : o < nArrs) (ha : a ∈ c.live) (hb : b ∈ c.live)
    (hoa : o ≠ a) (hob : o ≠ b) (hsl : sl ∈ c.kls) (bit : c.KV sl ≤ 1) :
    VP (St G c X) (sel o a b sl)
      (St G { c with A := KU c.A o (if c.KV sl = 0 then c.A a else c.A b), live := o :: c.live } X) := by
  refine ks_vp cert (fun σ s h => h.1) fun σ s ⟨h, x⟩ => ?_
  have hw := h.ws
  have va := h.arrs.get ha
  have vb := h.arrs.get hb
  have vs := h.ksl sl hsl
  refine h.ksOp (P := fun t => num t.mem G.KB G.w o =
      (if slot s.mem G.KB sl = 0 then num s.mem G.KB G.w a else num s.mem G.KB G.w b)) rfl
    ((sel_ok hw ho (h.liveOk a ha) (h.liveOk b hb) (by decide) hoa hob (h.kslOk sl hsl).1 (by show slot s.mem G.KB sl ≤ 1; rw [vs]; exact bit)).mono
      fun t ⟨w, k, v, r⟩ => ⟨w, k, v, r⟩)
    fun t k v R f => ⟨h.of_op R f ho k (by simp only [GP.ksState, State.withRegions_mem] at v; rw [v, va, vb, vs]), x⟩

/-- `[o] := [a]`. -/
theorem copy_vp {o a : Nat} (cert : Cert7 (copy o a)) (ho : o < nArrs) (ha : a ∈ c.live) (hoa : o ≠ a) :
    VP (St G c X) (copy o a) (St G { c with A := KU c.A o (c.A a), live := o :: c.live } X) := by
  refine ks_vp cert (fun σ s h => h.1) fun σ s ⟨h, x⟩ => ?_
  have hw := h.ws
  have va := h.arrs.get ha
  refine h.ksOp (P := fun t => num t.mem G.KB G.w o = num s.mem G.KB G.w a) rfl
    ((copy_ok hw ho (h.liveOk a ha) (by decide) hoa).mono fun t ⟨w, k, v, r, _⟩ => ⟨w, k, v, r⟩)
    fun t k v R f => ⟨h.of_op R f ho k (by simp only [GP.ksState, State.withRegions_mem] at v; rw [v, va]), x⟩

/-- The header word `sl` := `[j]`'s low bit. -/
theorem bitOf_vp {sl j : Nat} (cert : Cert7 (.block (bitOf sl j))) (hj : j ∈ c.live) (hsl : KlsOk sl) :
    VP (St G c X) (.block (bitOf sl j)) (St G { c with KV := KU c.KV sl (c.A j % 2), kls := sl :: c.kls } X) := by
  refine ks_vp cert (fun σ s h => h.1) fun σ s ⟨h, x⟩ => ?_
  have hw := h.ws
  have va := h.arrs.get hj
  refine h.ksOp (js := []) (ds := [sl]) (P := fun t => slot t.mem G.KB sl = num s.mem G.KB G.w j % 2) rfl
    (by rw [← List.append_nil (bitOf sl j)]
        exact bitOf_ok hw (h.liveOk j hj) (by decide) hsl.1 fun t w k v r => WP.block_nil ⟨w, k, v, r⟩)
    fun t k v R f => ⟨h.of_opS R f hsl k (by simp only [GP.ksState, State.withRegions_mem] at v; rw [v, va]), x⟩

/-- `[j]`'s low bit set. -/
theorem orOne_vp {j : Nat} (cert : Cert7 (.block (orOne j))) (hj : j ∈ c.live) :
    VP (St G c X) (.block (orOne j)) (St G { c with A := KU c.A j (2 * (c.A j / 2) + 1), live := j :: c.live } X) := by
  refine ks_vp cert (fun σ s h => h.1) fun σ s ⟨h, x⟩ => ?_
  have hw := h.ws
  have va := h.arrs.get hj
  refine h.ksOp (js := [j]) (ds := []) (P := fun t => num t.mem G.KB G.w j = 2 * (num s.mem G.KB G.w j / 2) + 1) rfl
    (by rw [← List.append_nil (orOne j)]
        exact orOne_ok hw (h.liveOk j hj) (by decide) fun t w k v r => WP.block_nil ⟨w, k, v, r⟩)
    fun t k v R f => ⟨h.of_op R f (h.liveOk j hj) k (by
      simp only [GP.ksState, State.withRegions_mem] at v; rw [v, va]), x⟩

/-- `[j]`'s low bit cleared. -/
theorem clrLow_vp {j : Nat} (cert : Cert7 (.block (clrLow j))) (hj : j ∈ c.live) :
    VP (St G c X) (.block (clrLow j)) (St G { c with A := KU c.A j (2 * (c.A j / 2)), live := j :: c.live } X) := by
  refine ks_vp cert (fun σ s h => h.1) fun σ s ⟨h, x⟩ => ?_
  have hw := h.ws
  have va := h.arrs.get hj
  refine h.ksOp (js := [j]) (ds := []) (P := fun t => num t.mem G.KB G.w j = 2 * (num s.mem G.KB G.w j / 2)) rfl
    (by rw [← List.append_nil (clrLow j)]
        exact clrLow_ok hw (h.liveOk j hj) (by decide) fun t w k v r _ => WP.block_nil ⟨w, k, v, r⟩)
    fun t k v R f => ⟨h.of_op R f (h.liveOk j hj) k (by
      simp only [GP.ksState, State.withRegions_mem] at v; rw [v, va]), x⟩

end

end VG.Proof.Dsa.Arm.Gen

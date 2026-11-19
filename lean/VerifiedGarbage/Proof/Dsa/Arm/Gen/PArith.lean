module

import VerifiedGarbage.Proof.Bignum.Arm.Zero
import VerifiedGarbage.Proof.Rsa.KeyWorkspace
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.Proof.Rsa.Arm.KeyWord
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Test
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.VP
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import VerifiedGarbage.Proof.Dsa.Encoding
public import VerifiedGarbage.Proof.Bignum.Arm.ReverseBuffer
import VerifiedGarbage.Proof.Rsa.Arm.CvStore
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Bytes
public import VerifiedGarbage.Proof.Framework.Arm.Call
public import VerifiedGarbage.Proof.Framework.Arm.Frame
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
public import VerifiedGarbage.Proof.Rsa.Arm.CvLoad
import VerifiedGarbage.Proof.Rsa.Arm.CvDivN
import VerifiedGarbage.Proof.Rsa.Arm.DivCT
import VerifiedGarbage.Proof.Rsa.Arm.KcStart
public import VerifiedGarbage.Impl.Rsa.Arm.CrtValues
public import VerifiedGarbage.Proof.Rsa.Arm.KeyWs
import VerifiedGarbage.Proof.Bignum.Arm.LoadBE
import VerifiedGarbage.Proof.Dsa.Arithmetic
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.Arm.KeyBits
public import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.Covers

/-! ### `Dsa.Arm.Gen.KSLoad`, which this module and modules that import it used -/

section

/-! ### `Dsa.Arm.Gen.KSOps`, which this module and modules that import it used -/

section

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

end

end

/-! ### `Dsa.Arm.Gen.KSDiv`, which only this module used -/

section

/-! # DSA parameter generation on ARMv7: the division

`divHdr_vp`: the division's header; `div_vp`: the division
(`Impl/Rsa/Arm/Div.lean`, `Proof/Rsa/Arm/CvLoad.lean`), which changes `r7`
and `r9` (`SS79`: a state of the search once they are set back); `wRegs_vp`:
`r9` and `r7` set back. The division's constant time is proven on the state
narrowed to the key working space (`RelCT.narrow`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.Proof.Mont VG.Proof.Rsa.Arm.Keys
open VG.Impl.Dsa.Arm.Generation
open VG.Impl.Rsa.Arm.Keys (hdr stride)
open VG.Impl.Rsa.Arm.CrtValues (divHdr)
open VG.Proof.X25519.Arm (Rest Upd wp_mov op2_imm)
open VG.Proof.Rsa.Arm.Recover (VP)

/-- Two runs of `c` leak the same trace if its runs from the states narrowed
to the regions `rd`, `wr` do, and exist (as `Proof/MlDsa/Arm/Pack/HintBase.lean`). -/
theorem RelCT.narrow {c : Prog isa} {P : State → State → Prop} (rd wr : State → List Region)
    (hc : ∀ a b, P a b → Covers (rd a ++ wr a) (a.rd ++ a.wr) ∧ Covers (wr a) a.wr ∧
      Covers (rd b ++ wr b) (b.rd ++ b.wr) ∧ Covers (wr b) b.wr)
    (hrun : ∀ a b, P a b → (∃ t s', Exec isa c (a.withRegions (rd a) (wr a)) t s') ∧
      ∃ t s', Exec isa c (b.withRegions (rd b) (wr b)) t s')
    (hct : RelCT isa (fun a' b' => ∃ a b, P a b ∧ a' = a.withRegions (rd a) (wr a) ∧
      b' = b.withRegions (rd b) (wr b)) c fun _ _ => True) :
    RelCT isa P c fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨c₁, w₁, c₂, w₂⟩ := hc _ _ hp
  obtain ⟨⟨u₁, n₁, f₁⟩, ⟨u₂, n₂, f₂⟩⟩ := hrun _ _ hp
  have g₁ := Exec.widen f₁ (rd := s₁.rd) (wr := s₁.wr) (by simpa using c₁) (by simpa using w₁)
  have g₂ := Exec.widen f₂ (rd := s₂.rd) (wr := s₂.wr) (by simpa using c₂) (by simpa using w₂)
  simp only [State.withRegions_withRegions, State.withRegions_self] at g₁ g₂
  obtain ⟨rfl, -⟩ := Exec.det e₁ g₁
  obtain ⟨rfl, -⟩ := Exec.det e₂ g₂
  exact ⟨(hct _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ f₁ f₂).1, trivial⟩

/-- Every register. -/
abbrev allRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]

theorem mem_allRegs (r : Reg) : r ∈ allRegs := by cases r <;> decide

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- A state of the search once `r7` and `r9` are set back. -/
def SS79 (G : GP) (σ : State) (c : Cfg) (t : State) : Prop :=
  ∀ t' : State, t'.mem = t.mem → t'.sp = t.sp → t'.rd = t.rd → t'.wr = t.wr → t'.gpr .r8 = t.gpr .r8 →
    t'.gpr .r7 = BitVec.ofNat 32 (S G.w) → t'.gpr .r9 = BitVec.ofNat 32 G.w → SS G σ c t'

/-- The top word of array `d`. -/
abbrev Top (G : GP) (m : Mem) (d : Nat) : Prop := w32 m (State.addr G.KB) (arr G.w d + 4 * G.w) = 0

/-- `r9` and `r7` set back. -/
theorem wRegs_vp {L : Nat} (hL : L = G.pLen) (hlq : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384) :
    VP (fun σ t => SS79 G σ c t ∧ X σ) (.block (wRegs L)) (St G c X) := by
  refine VP.taint [] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs []) (.block (wRegs 128)), rfl⟩
    (fun _ _ _ _ _ _ r hr => absurd hr (by simp)) fun σ s ⟨h, x⟩ => ?_
  subst hL
  have w96 : G.pLen / 4 < 256 := by omega_using [hlq]
  refine wp_mov (op2_imm (encodable_lt w96)) fun s₁ u₁ => ?_
  refine VG.Proof.Rsa.Arm.KeyCheck.stride_ok (w := G.w) (by simp only [GP.w]; omega_using [hlq]) u₁.gpr fun t e7 R m => ?_
  refine WP.block_nil ⟨h t (m.trans u₁.mem) (R.sp.trans u₁.sp) (R.rd.trans u₁.rd) (R.wr.trans u₁.wr)
    (by rw [R.gpr _ (by decide), u₁.other _ (by decide)]) e7 (by rw [R.gpr _ (by decide), u₁.gpr]), x⟩

/-- The division's header: the arrays `q`, `r`, `d` and `t`, with the
count already at word 16. -/
theorem divHdr_vp {q r d t : Nat} (cert : Cert7 (.block (divHdr q r d t))) (hq : q < 256) (hr : r < 256)
    (hd : d < nArrs) (ht : t < 256) (h16 : 16 ∈ c.kls) (hv16 : c.KV 16 = G.w) (hkls : ∀ e ∈ c.kls, 16 ≤ e) :
    VP (fun σ s => St G c X σ s ∧ Top G s.mem d) (.block (divHdr q r d t))
      (fun σ s => St G c X σ s ∧ Top G s.mem d ∧ DivHdr s.mem G.KB G.w q r d t) := by
  refine ks_vp cert (fun σ s h => h.1.1) fun σ s ⟨⟨h, x⟩, top⟩ => ?_
  have hw := h.ws
  have cnt : s.mem.readW (off (State.addr G.KB) 16) 32 = BitVec.ofNat 32 G.w := by
    have e := h.ksl 16 h16
    rw [hv16] at e
    apply BitVec.eq_of_toNat_eq
    rw [← show slot s.mem G.KB 16 = (s.mem.readW (off (State.addr G.KB) 16) 32).toNat from rfl, e,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hw.wle; omega_using [this])]
  refine h.ksOp (js := []) (ds := [0, 4, 8, 12]) (P := fun u => DivHdr u.mem G.KB G.w q r d t) rfl
    (by rw [← List.append_nil (divHdr q r d t)]
        exact VG.Proof.Rsa.Arm.CrtValues.divHdr_ok hw hq hr (by simp only [nArrs] at hd; omega_using [hd]) ht cnt fun u w k v R => WP.block_nil ⟨w, k, v, R⟩)
    fun u k v R f => ⟨⟨?_, x⟩, ?_, v⟩
  · have sl : ∀ e ∈ c.kls, slot u.mem G.KB e = c.KV e := fun e he => by
      have h16' := hkls e he
      have ap : ∀ d' ∈ [0, 4, 8, 12], e + 4 ≤ d' ∨ d' + 4 ≤ e := by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro d' (rfl | rfl | rfl | rfl) <;> omega_using [h16']
      rw [k.slot (h.kslOk e he).1 ap]
      exact h.ksl e he
    exact h.of_ks R f (h.arrs.keep k hw (fun j hj => ⟨h.liveOk j hj, by simp⟩) (by simp [hdr])) h.liveOk sl
      h.kslOk
  · have := hw.wle
    show w32 u.mem _ _ = 0
    rw [show arr G.w d + 4 * G.w = arr G.w d + 4 * G.w from rfl,
      k.word (j := d) (i := G.w) (by simp only [S]; omega_using []) (by simp) (by simp [hdr]) (hw.fit64 hd)]
    exact top

/-- The stage after the division. -/
abbrev divCfg (c : Cfg) (q r d : Nat) : Cfg :=
  { c with A := KU (KU c.A q (c.A q / c.A d)) r (c.A q % c.A d), live := q :: r :: c.live }

/-- The division: `[q] := [q] / [d]`, `[r] := [q] mod [d]`, the temporary `t`
lost, and `r7` and `r9` changed. -/
theorem div_vp {q r d t : Nat} (hq : q < nArrs) (hr : r < nArrs) (hd : d < nArrs) (ht : t < nArrs)
    (hqr : q ≠ r) (hqd : q ≠ d) (hqt : q ≠ t) (hrd : r ≠ d) (hrt : r ≠ t) (hdt : d ≠ t)
    (hqL : q ∈ c.live) (hdL : d ∈ c.live) (htL : t ∉ c.live) (hpos : 0 < c.A d) :
    VP (fun σ s => St G c X σ s ∧ Top G s.mem d ∧ DivHdr s.mem G.KB G.w q r d t) VG.Impl.Rsa.Arm.Div.code
      (fun σ s => SS79 G σ (divCfg c q r d) s ∧ X σ) := by
  have run : ∀ σ s, St G c X σ s → Top G s.mem d → DivHdr s.mem G.KB G.w q r d t →
      WP isa VG.Impl.Rsa.Arm.Div.code (G.ksState s) fun u => Keep G.KB G.w [q, r, t] [] s.mem u.mem ∧
        Rest (.r6 :: VG.Proof.Rsa.Arm.Div.clobbers) (G.ksState s) u ∧
        (0 < num s.mem G.KB G.w d → num u.mem G.KB G.w r = num s.mem G.KB G.w q % num s.mem G.KB G.w d ∧
          num u.mem G.KB G.w q = num s.mem G.KB G.w q / num s.mem G.KB G.w d) :=
    fun σ s ⟨h, _⟩ top hh => div_ok h.ws hq hr hd ht hqr hqd hqt hrd hrt hdt hh top
  refine VP.of_ct (fun σ₁ σ₂ => ?_) fun σ s ⟨⟨h, x⟩, top, hh⟩ => ?_
  · refine RelCT.narrow (fun a => a.rd) (fun _ => [G.rK]) (fun a b ⟨⟨⟨ha, _⟩, _⟩, ⟨⟨hb, _⟩, _⟩⟩ =>
      ⟨ha.kcov.1, ha.kcov.2, hb.kcov.1, hb.kcov.2⟩) (fun a b ⟨⟨ha, ta, da⟩, ⟨hb, tb, db⟩⟩ =>
      ⟨let ⟨t, s', e, _⟩ := run _ _ ha ta da; ⟨t, s', e⟩, let ⟨t, s', e, _⟩ := run _ _ hb tb db; ⟨t, s', e⟩⟩) ?_
    refine (VG.Proof.Rsa.Arm.Div.code_ct (g := divGeom G.KB (kz G.pLen) G.w q r d t)).mono
      (fun a' b' ⟨a, b, ⟨⟨⟨ha, _⟩, _, da⟩, ⟨⟨hb, _⟩, _, db⟩⟩, ea, eb⟩ => ?_) fun _ _ _ => trivial
    subst ea eb
    exact ⟨divGeom_ctx ha.ws hq hr hd ht hqr hqd hqt hrd hrt hdt da,
      divGeom_ctx hb.ws hq hr hd ht hqr hqd hqt hrd hrt hdt db⟩
  refine h.ksWP rfl (run σ s ⟨h, x⟩ top hh) fun u ⟨k, R, v⟩ hr' hw' f => ⟨fun t' m sp rd wr e8 e7 e9 => ?_, x⟩
  have hw := h.ws
  have va := h.arrs.get hqL
  have vd := h.arrs.get hdL
  obtain ⟨vr, vq⟩ := v (by rw [vd]; exact hpos)
  simp only [GP.ksState, State.withRegions_mem] at vr vq k
  rw [va, vd] at vr vq
  have R' : Rest allRegs s t' := ⟨fun r hr => absurd (mem_allRegs r) hr, rd.trans hr', wr.trans hw',
    sp.trans (R.sp)⟩
  have e8' : t'.gpr .r8 = G.KB := by
    rw [e8]; exact (R.gpr .r8 (by decide)).trans h.r8
  refine h.of_ks' R' (m ▸ f) (fun j hj => ?_) (fun j hj => ?_) (fun e he => ?_) h.kslOk e7 e8' e9
  · rw [m]
    simp only [List.mem_cons] at hj
    show num u.mem G.KB G.w j = KU (KU c.A q (c.A q / c.A d)) r (c.A q % c.A d) j
    simp only [KU]
    by_cases ejr : j = r
    · subst ejr; rw [VG.Proof.Rsa.Arm.Keys.upd_self]; exact vr
    rw [VG.Proof.Rsa.Arm.Keys.upd_ne _ _ ejr]
    by_cases ejq : j = q
    · subst ejq; rw [VG.Proof.Rsa.Arm.Keys.upd_self]; exact vq
    rw [VG.Proof.Rsa.Arm.Keys.upd_ne _ _ ejq]
    have jl : j ∈ c.live := by rcases hj with rfl | rfl | hj <;> first | exact absurd rfl ejq | exact absurd rfl ejr | exact hj
    have ejt : j ≠ t := fun e => htL (e ▸ jl)
    rw [k.num (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro k' (rfl | rfl | rfl) <;> omega_arith)
      (by simp) (hw.fit64 (h.liveOk j jl))]
    exact h.arrs.get jl
  · simp only [List.mem_cons] at hj
    rcases hj with rfl | rfl | hj
    · exact hq
    · exact hr
    · exact h.liveOk j hj
  · rw [m, k.slot (h.kslOk e he).1 (by simp)]; exact h.ksl e he

end

end VG.Proof.Dsa.Arm.Gen

end

end


/-! # DSA parameter generation on ARMv7: numbers into the key working space

`loadS L j o n` (`loadS_vp`): array `j` := the `n` big-endian bytes that a
claim puts at byte `o` of `scratch`, its words above them zero (`Top`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.Proof.Mont VG.Proof.Rsa.Arm.Keys
open VG.Impl.Dsa.Arm.Generation
open VG.Impl.Rsa.Arm.Keys (hdr ptr)
open VG.Proof.X25519.Arm (Rest Upd wp_mov wp_movw wp_dp op2_imm op2_reg dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)

/-- The top word of a number of `w + 2` words below `2^(32 w)`. -/
theorem top_of_lt {m : Mem} {base : Addr} {d w : Nat} (h : val32 m base d (w + 2) < 2 ^ (32 * w)) :
    w32 m base (d + 4 * w) = 0 := by
  have e := val32_append m base d w 2
  have lo := val32_lt m base d w
  have p := Nat.two_pow_pos (32 * w)
  have z : val32 m base (d + 4 * w) 2 = 0 := by
    rcases Nat.eq_zero_or_pos (val32 m base (d + 4 * w) 2) with z | z
    · exact z
    · have : 2 ^ (32 * w) * 1 ≤ 2 ^ (32 * w) * val32 m base (d + 4 * w) 2 := Nat.mul_le_mul_left _ z
      omega_using [h, e, this]
  have e2 := val32_append m base (d + 4 * w) 1 1
  rw [show 1 + 1 = 2 from rfl, z] at e2
  simp only [val32, Nat.add_zero, Nat.mul_zero] at e2
  omega_using [e2]

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- A taint certificate for a load, its source and length public. -/
abbrev CertL (j : Nat) : Prop := ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r6, .r7, .r8, .r9])
  (VG.Impl.Rsa.Arm.CrtValues.load j) hc).isSome = true

/-- Array `j` := the `n` bytes `bs` at `r4` (`r6 = n`), readable and apart from the key working space. -/
theorem loadAt_vp {j n : Nat} {src : BitVec 32} {bs : List Byte} (cert : CertL j) (hj : j < nArrs) (hn : bs.length = n)
    (hn0 : 0 < n) (hnw : n ≤ 4 * G.w)
    (hsrc : ∀ σ s, St G c X σ s → Covers [⟨State.addr src, n⟩] (s.rd ++ s.wr) ∧
      Region.Disjoint ⟨State.addr src, n⟩ G.rK ∧ src.toNat + n ≤ 2 ^ 32 ∧
      Spec.Rsa.bytesAt s.mem (State.addr src) n = bs) :
    VP (fun σ s => St G c X σ s ∧ s.gpr .r4 = src ∧ s.gpr .r6 = BitVec.ofNat 32 n)
      (VG.Impl.Rsa.Arm.CrtValues.load j)
      (fun σ t => St G { c with A := KU c.A j (Spec.Dsa.decodeBE bs), live := j :: c.live } X σ t ∧
        Top G t.mem j) := by
  refine VP.taint [.r4, .r6, .r7, .r8, .r9] cert
    (fun σ₁ σ₂ s₁ s₂ ⟨⟨h₁, _⟩, a₁, b₁⟩ ⟨⟨h₂, _⟩, a₂, b₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [a₁, a₂]
      · rw [b₁, b₂]
      · rw [h₁.r7, h₂.r7]
      · rw [h₁.r8, h₂.r8]
      · rw [h₁.r9, h₂.r9]) fun σ s ⟨⟨h, x⟩, p4, p6⟩ => ?_
  obtain ⟨hR, sep, sfit, b⟩ := hsrc σ s ⟨h, x⟩
  have gi := h.gi
  have l := h.lens
  have hw := h.wsWith (s.rd ++ [⟨State.addr src, n⟩])
  have nw := hw.nowrap
  have fa := hw.arr_fit hj
  have hS : S G.w = 4 * (G.w + 2) := rfl
  have w96 : G.w ≤ 96 := by simp only [GP.w]; omega_using [l]
  have ad : State.addr (G.KB + BitVec.ofNat 32 (arr G.w j)) = off (State.addr G.KB) (arr G.w j) :=
    hw.addr (by omega_using [fa, hS])
  have hrk : Region.Sub ⟨off (State.addr G.KB) (arr G.w j), 4 * (G.w + 2)⟩ G.rK :=
    Offset.sub_base (State.addr G.KB) (by omega_using [fa, hS])
  refine h.ksWPr hR rfl (P := fun t =>
      val32 t.mem (State.addr (G.KB + BitVec.ofNat 32 (arr G.w j))) 0 (G.w + 2) = Spec.Rsa.os2ip bs ∧
      Frame [⟨State.addr (G.KB + BitVec.ofNat 32 (arr G.w j)), 4 * (G.w + 2)⟩] s.mem t.mem ∧
      Rest [.r0, .r1, .r2, .r3, .r5, .lr] (s.withRegions (s.rd ++ [⟨State.addr src, n⟩]) [G.rK]) t) ?_ ?_
  · unfold VG.Impl.Rsa.Arm.CrtValues.load
    refine WP.seq (ptr_ok hw (r := .r0) (by decide) (by simp only [nArrs] at hj; omega_using [hj]) fun s₃ p₃ R₃ m₃ hw₃ => ?_)
    refine wp_mov (op2_reg _ _) fun s₄ u₄ => ?_
    refine wp_dp (op2_imm (by decide)) fun s₅ u₅ => ?_
    refine wp_mov (op2_imm (by decide)) fun s₆ u₆ => WP.block_nil ?_
    have mem6 : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, m₃]; rfl
    have R₆ : Rest [.r0, .r3, .r5, .lr] (s.withRegions (s.rd ++ [⟨State.addr src, n⟩]) [G.rK]) s₆ :=
      (R₃.mono (by simp)).trans ((u₄.rest (by simp)).trans ((u₅.rest (by simp)).trans (u₆.rest (by simp))))
    have p0 : s₆.gpr .r0 = G.KB + BitVec.ofNat 32 (arr G.w j) := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), p₃]
    refine WP.mono (VG.Proof.Bignum.Arm.loadBE_ok s₆ (src := src)
      (dst := G.KB + BitVec.ofNat 32 (arr G.w j)) (n := G.w + 2) (k := n) hn0 (by omega_using [hnw]) (by omega_using [hnw, w96]) sfit
      (by rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat]; omega_using [nw, fa, hS]), BitVec.toNat_ofNat]; omega_using [nw, fa, hS])
      ⟨⟨State.addr src, n⟩, List.mem_append_left _ (by rw [R₆.rd]; simp), Region.contains_self _ _⟩
      ⟨G.rK, by rw [R₆.wr]; exact List.mem_singleton_self _, by
        rw [ad]; exact Offset.contains_base (State.addr G.KB) (by omega_using [fa, hS]) (by omega_using [nw, fa])⟩
      (by rw [ad]; exact sep.sub_right hrk)
      p0 (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), R₃.gpr _ (by decide)]; exact p4)
      (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, p₃])
      (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), R₃.gpr _ (by decide)]; exact p6)
      (by rw [u₆.other _ (by decide), u₅.gpr, dpVal, u₄.other _ (by decide), R₃.gpr _ (by decide), hw.r9,
        BitVec.ofNat_add]; rfl)
      (by rw [u₆.gpr])) ?_
    rintro t ⟨v, f, r⟩
    refine ⟨?_, ?_, (R₆.mono (by simp)).trans (r.mono (by simp))⟩
    · rw [v, mem6, b]
    · rw [← mem6]; exact f
  · intro t ⟨v, f, R⟩ hr hw' fK
    simp only [State.withRegions_mem] at v
    rw [ad] at v f
    have k : Keep G.KB G.w [j] [] s.mem t.mem := VG.Proof.Rsa.Arm.CrtValues.Keep.of_frame_arr f (by omega_using [nw, fa])
    rw [VG.Proof.Rsa.Arm.CrtValues.val32_off, Nat.add_zero] at v
    have lt : Spec.Rsa.os2ip bs < 2 ^ (32 * G.w) := by
      have := VG.Proof.Dsa.decodeBE_lt bs
      rw [hn, VG.Proof.Dsa.decodeBE_os2ip] at this
      refine Nat.lt_of_lt_of_le this ?_
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
      exact Nat.pow_le_pow_right (by decide) (by omega_using [hnw])
    have vw : num t.mem G.KB G.w j = Spec.Dsa.decodeBE bs := by
      rw [VG.Proof.Dsa.decodeBE_os2ip, ← v]
      exact VG.Proof.Rsa.Arm.CrtValues.val32_low2 (by rw [v]; exact lt)
    have R' : Rest [.r0, .r1, .r2, .r3, .r5, .lr] s t := ⟨R.gpr, hr, hw', R.sp⟩
    exact ⟨⟨h.of_op R' fK hj k vw, x⟩, top_of_lt (by rw [v]; exact lt)⟩

/-- Array `j` := the bytes `bs` that a claim puts at byte `o` of `scratch`. -/
theorem loadS_vp {L j o n : Nat} {bs : List Byte} (cert : CertL j) (hL : L = G.pLen) (hj : j < nArrs) (hbs : (o, bs) ∈ c.cl)
    (hn : bs.length = n) (hn0 : 0 < n) (hnw : n ≤ 4 * G.w) :
    VP (St G c X) (loadS L j o n)
      (fun σ t => St G { c with A := KU c.A j (Spec.Dsa.decodeBE bs), live := j :: c.live } X σ t ∧
        Top G t.mem j) := by
  subst hL
  refine VP.seq (G := fun σ s => St G c X σ s ∧ s.gpr .r4 = G.scr + BitVec.ofNat 32 o ∧
      s.gpr .r6 = BitVec.ofNat 32 n) (VP.taint [.r8] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r8])
      (.block (scr 128 .r4 0 ++ [.movw .r6 (BitVec.ofNat 16 20)])), rfl⟩
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.r8, h₂.1.r8])
    fun σ s ⟨h, x⟩ => ?_) (loadAt_vp cert hj hn hn0 hnw fun σ s ⟨h, x⟩ => ?_)
  · have big := h.gi.scrBig
    have oK : o + n ≤ sK G.pLen := by have := h.clOk _ hbs; simpa [hn] using this
    have w96 : G.w ≤ 96 := by have := h.lens; simp only [GP.w]; omega_using [this]
    refine scr_ok (d := .r4) (o := o) h.r8 rfl h.lens (by omega_using [oK]) fun s₁ v₁ R₁ M₁ => wp_movw fun s₂ u₂ =>
      WP.block_nil ⟨⟨h.of_rest ((R₁.mono (by simp)).trans (u₂.rest (by simp)) : Rest [.r12, .r4, .r6] s s₂)
        (by rw [u₂.mem, M₁]), x⟩, by
        rw [u₂.other _ (by decide), v₁], by rw [u₂.gpr, setWidth_ofNat16 (by omega_using [hnw, w96])]⟩
  · have gi := h.gi
    have big := gi.scrBig
    have fit := gi.scrFit
    have oK : o + n ≤ sK G.pLen := by have := h.clOk _ hbs; simpa [hn] using this
    have kz0 : 0 < kz G.pLen := by simp only [kz]; omega_using []
    have inS : G.rScr ∈ s.wr := by rw [gi.wr, gi.pre.wr, gi.hG]; simp
    have as : State.addr (G.scr + BitVec.ofNat 32 o) = G.sa o := gi.saddr (by omega_using [hn0, big, oK])
    have b := h.sb _ hbs
    simp only [hn] at b
    rw [as]
    refine ⟨(Covers.of_sub (rs' := [G.rScr]) fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact ⟨G.rScr, List.mem_singleton_self _, o, rfl, show o + n ≤ G.scrLen * 8 by omega_using [big, oK]⟩).trans
      (Covers.of_mem fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact List.mem_append_right _ inS),
      ?_, ?_, b⟩
    · show Region.Disjoint _ ⟨State.addr G.KB, _⟩
      rw [gi.kaddr]; exact gi.sdisj (.inl oK) (by omega_using [big, oK]) big
    · rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat]; omega_using [hn0, big, fit, oK]), BitVec.toNat_ofNat]; omega_using [big, fit, oK]

end

end VG.Proof.Dsa.Arm.Gen

end

end

/-! ### `Dsa.Arm.Gen.Intro`, which the modules that import this one used -/

section

/-! # DSA parameter generation on ARMv7: a stage's pure facts as hypotheses -/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Proof.Rsa.Arm.Recover (VP)

/-- A stage's pure facts, as hypotheses. -/
theorem VP.intro {P : Prop} {F Q : State → State → Prop} {c : Prog isa} (h : P → VP F c Q) :
    VP (fun σ s => P ∧ F σ s) c Q := by
  by_cases hp : P
  · exact (h hp).mono (fun σ s h => h.2) fun _ _ h => h
  · exact VP.of_false fun σ s h => hp h.1

end VG.Proof.Dsa.Arm.Gen

end

end

/-! ### `Dsa.Arm.Gen.KSStore`, which this module and modules that import it used -/

section

/-! # DSA parameter generation on ARMv7: numbers out of the key working space

`storeBE L j o n` (`storeBE_vp`): the claim at byte `o` of `scratch` := the
low `n` bytes of array `j`, big-endian.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.Proof.Mont VG.Proof.Rsa.Arm.Keys
open VG.Impl.Dsa.Arm.Generation
open VG.Impl.Rsa.Arm.Keys (hdr ptr)
open VG.Proof.X25519.Arm (Rest Upd wp_mov wp_movw wp_dp wp_mul op2_imm op2_reg dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)

section
variable {G : GP} {σ : State} {c : Cfg} {s : State}

/-- The pointer to array `j`, from a state of the search. -/
theorem SS.ptr_ok (h : SS G σ c s) {r : Reg} (hr : r ∉ [.r7, .r8, .r9]) {j : Nat} (hj : j < 256)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr r = G.KB + BitVec.ofNat 32 (arr G.w j) → Rest [r] s t → t.mem = s.mem →
      WP isa (.block rest) t Q) :
    WP isa (.block (ptr r j ++ rest)) s Q := by
  have r7 : r ≠ .r7 := fun e => hr (by simp [e])
  have r8 : r ≠ .r8 := fun e => hr (by simp [e])
  exact ptr_regs_ok r7 r8 hj h.r7 h.r8 k

end

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- The claim at byte `o` of `scratch` := `[j]`'s low `n` bytes, big-endian. -/
theorem storeBE_vp {L j o n : Nat} (cert : Cert7 (storeBE L j o n)) (hL : L = G.pLen) (hj : j ∈ c.live)
    (hn0 : 0 < n) (hnw : n ≤ 4 * G.w) (hoK : o + n ≤ sK G.pLen) {cl' : Claims}
    (hcl : ∀ x ∈ cl', x ∈ c.cl ∧ Apart o n x) :
    VP (St G c X) (storeBE L j o n)
      (St G { c with cl := (o, Spec.Rsa.i2osp (c.A j % 2 ^ (8 * n)) n) :: cl' } X) := by
  refine ks_vp cert (fun σ s h => h.1) fun σ s ⟨h, x⟩ => ?_
  subst hL
  have gi := h.gi
  have big := gi.scrBig
  have fit := gi.scrFit
  have l := h.lens
  have kb := h.kbNat
  have hjN := h.liveOk j hj
  have fa : arr G.w j + S G.w ≤ kz G.pLen := (h.ws).arr_fit hjN
  have hS : S G.w = 4 * (G.w + 2) := rfl
  have w96 : G.w ≤ 96 := by simp only [GP.w]; omega_using [l]
  have inS : G.rScr ∈ s.wr := by rw [gi.wr, gi.pre.wr, gi.hG]; simp
  have ad : State.addr (G.KB + BitVec.ofNat 32 (arr G.w j)) = off (State.addr G.KB) (arr G.w j) :=
    h.ws.addr (by omega_using [fa, hS])
  have e : off (State.addr G.KB) (arr G.w j) = G.sa (sK G.pLen + arr G.w j) := by
    rw [gi.kaddr]; simp only [off, GP.sa]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have as : State.addr (G.scr + BitVec.ofNat 32 o) = G.sa o := gi.saddr (by omega_using [hn0, hoK, big])
  have va := h.arrs.get hj
  unfold storeBE
  simp only [List.append_assoc]
  refine WP.seq (h.ptr_ok (r := .r1) (j := j) (by decide) (by simp only [nArrs] at hjN; omega_using [hjN]) fun s₁ p₁ R₁ m₁ => ?_)
  refine wp_movw fun s₂ u₂ => ?_
  refine wp_dp (op2_reg _ _) fun s₃ u₃ => ?_
  have r8₃ : s₃.gpr .r8 = G.KB := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), R₁.gpr _ (by decide), h.r8]
  refine scr_ok (d := .r0) (o := o) r8₃ rfl l (by omega_using [hoK]) fun s₄ v₄ R₄ M₄ => ?_
  refine wp_movw fun s₅ u₅ => WP.block_nil ?_
  have R₅ : Rest [.r0, .r1, .r2, .r12, .lr] s s₅ := (R₁.mono (by simp)).trans ((u₂.rest (by simp)).trans
    ((u₃.rest (by simp)).trans ((R₄.mono (by simp)).trans (u₅.rest (by simp)))))
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, M₄, u₃.mem, u₂.mem, m₁]
  have wr₅ : s₅.wr = s.wr := R₅.wr
  have srcFit : (G.KB + BitVec.ofNat 32 (arr G.w j)).toNat + n ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat]; omega_using [big, fit, kb, fa, hS]), BitVec.toNat_ofNat]; omega_using [hnw, big, fit, kb, fa, hS]
  have dstFit : (G.scr + BitVec.ofNat 32 o).toNat + n ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat]; omega_using [hoK, kb]), BitVec.toNat_ofNat]; omega_using [hoK, kb]
  refine WP.mono (VG.Proof.Bignum.Arm.reverseBuffer_ok s₅ (src := G.KB + BitVec.ofNat 32 (arr G.w j)) (dst := G.scr + BitVec.ofNat 32 o)
    (n := n) hn0 srcFit dstFit (by omega_using [hoK, kb])
    ⟨G.rScr, List.mem_append_right _ (by rw [wr₅]; exact inS), by
      rw [ad, e]; exact Offset.contains_base _ (by omega_using [hnw, big, fa, hS]) (by omega_using [big, fit, fa])⟩
    ⟨G.rScr, by rw [wr₅]; exact inS, by rw [as]; exact Offset.contains_base _ (by omega_using [hoK, big]) (by omega_using [hoK, big, fit])⟩
    (by rw [ad, e, as]; exact gi.sdisj (.inr (by omega_using [hoK])) (by omega_using [hnw, big, fa, hS]) (by omega_using [hoK, big]))
    (by rw [u₅.other _ (by decide), v₄])
    (by rw [u₅.other _ (by decide), R₄.gpr _ (by decide), u₃.gpr, dpVal, u₂.gpr, u₂.other _ (by decide), p₁,
      setWidth_ofNat16 (by omega_using [hnw, w96])])
    (by rw [u₅.gpr, setWidth_ofNat16 (by omega_using [hnw, w96])])) ?_
  rintro t ⟨bt, ft, _, rt⟩
  rw [as, ad, m₅, VG.Proof.Rsa.Arm.CrtValues.read_low _ _ (n := G.w) hnw,
    show val32 s.mem (State.addr G.KB) (arr G.w j) G.w = num s.mem G.KB G.w j from rfl, va] at bt
  rw [as, m₅] at ft
  refine ⟨h.of_scr (R₅.trans (rt.mono (by simp))) (o := o) (n := n) hoK (ft.mono (by simp)) fun y hy => ?_, x⟩
  rcases List.mem_cons.mp hy with rfl | hy
  · exact .inr ⟨by rw [VG.Proof.Rsa.i2osp_length]; exact bt, by rw [VG.Proof.Rsa.i2osp_length]; exact hoK⟩
  · exact .inl (hcl y hy)

end

end VG.Proof.Dsa.Arm.Gen

end

end

/-! ### `Dsa.Arm.Gen.KSSetup`, which only this module used -/

section

/-! # DSA parameter generation on ARMv7: the key working space set up

`ksSetup` (`ksSetup_vp`): the count `w` into the division's header (word
16), every array zeroed, and `[aOne] := 1`.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.Proof.Mont VG.Proof.Rsa.Arm.Keys
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.Bignum.Arm (zero_ok ZeroInv)
open VG.Impl.Rsa.Arm.Keys (hdr setOne)
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp wp_mul op2_imm op2_reg op2_lsr dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)

/-- The arrays after the setup: all zero but `[aOne] = 1`. -/
abbrev A0 : Nat → Nat := KU (fun _ => 0) aOne 1

/-- Every array. -/
abbrev allArrs : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]

theorem allArrs_lt : ∀ j ∈ allArrs, j < nArrs := by decide

section
variable {G : GP} {c : Cfg} {X : State → Prop}

theorem ksSetup_vp :
    VP (St G c X) ksSetup (St G { c with A := A0, live := allArrs, KV := KU c.KV 16 G.w, kls := [16] } X) := by
  refine ks_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9]) ksSetup, by kernel_rfl⟩
    (fun σ s h => h.1) fun σ s ⟨h, x⟩ => ?_
  have hw := h.ws
  have l := h.lens
  have nw := hw.nowrap
  have wl : G.w ≤ 96 := by simp only [GP.w]; omega_using [l]
  have w1 : 1 ≤ G.w := by simp only [GP.w]; omega_using [l]
  have fits : hdr + 4 * (nArrs * (G.w + 2)) ≤ kz G.pLen := by
    simp only [hdr, nArrs, kz, GP.w]; omega_using [l]
  refine h.ksWP rfl (P := fun t => Arrs t.mem G.KB G.w A0 allArrs ∧ slot t.mem G.KB 16 = G.w ∧
      Rest VG.Proof.Rsa.Arm.Keys.opRegs (G.ksState s) t) ?_
    fun t ⟨a, sl, R⟩ hr hw' f => ⟨?_, x⟩
  swap
  · have R' : Rest VG.Proof.Rsa.Arm.Keys.opRegs s t := ⟨R.gpr, hr, hw', R.sp⟩
    have hk : ∀ d ∈ [16], slot t.mem G.KB d = KU c.KV 16 G.w d := fun d hd => by
      rw [List.mem_singleton] at hd; subst hd
      rw [KU, VG.Proof.Rsa.Arm.Keys.upd_self]; exact sl
    have hko : ∀ d ∈ [16], KlsOk d := fun d hd => by
      rw [List.mem_singleton] at hd; subst hd; decide
    exact h.of_ks R' f a allArrs_lt hk hko
  -- The count, the pointer and the number of words.
  unfold ksSetup
  refine WP.seq (wp_strSlot hw (d := 16) (by decide) fun s₁ u₁ => ?_)
  have hw₁ := hw.of_mupd u₁
  have o₁ := writeW32_outside (G.ksState s).mem (State.addr G.KB) (d := 16) ((G.ksState s).gpr .r9) (by decide)
  rw [← u₁.mem] at o₁
  refine wp_dp (op2_imm (by decide)) fun s₂ u₂ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₃ u₃ => ?_
  refine wp_mul fun s₄ u₄ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₅ u₅ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₆ u₆ => WP.block_nil ?_
  have R₆ : Rest [.r0, .lr, .r3] s₁ s₆ := (u₂.rest (by simp)).trans ((u₃.rest (by simp)).trans
    ((u₄.rest (by simp)).trans ((u₅.rest (by simp)).trans (u₆.rest (by simp)))))
  have m₆ : s₆.mem = s₁.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  have hw₆ := hw₁.rest R₆
  have p0 : s₆.gpr .r0 = G.KB + BitVec.ofNat 32 hdr := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      dpVal, hw₁.r8]
  have plr : s₆.gpr .lr = BitVec.ofNat 32 (nArrs * (G.w + 2)) := by
    rw [u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.other _ (by decide), hw₁.r7]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_mul, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp only [nArrs, S]
    rw [Nat.mod_eq_of_lt (a := 15) (by decide), Nat.mod_eq_of_lt (a := 4 * (G.w + 2)) (by omega_using [wl]),
      Nat.mod_eq_of_lt (a := 15 * (4 * (G.w + 2))) (by omega_using [wl]), Nat.mod_eq_of_lt (a := 15 * (G.w + 2)) (by omega_using [wl])]
    omega_using []
  have p3 : s₆.gpr .r3 = 0 := u₆.gpr
  -- Zero, then 1.
  refine WP.seq (WP.mono (zero_ok s₆ (base := G.KB) (size := kz G.pLen) (o := hdr) (n := nArrs * (G.w + 2))
    ⟨nw, fits, ⟨G.rK, by rw [R₆.wr, u₁.wr]; exact List.mem_singleton_self _, Region.contains_self _ _⟩⟩
    (by simp only [nArrs]; omega_using []) p0 plr p3) fun s₇ z => ?_)
  have hw₇ := hw₆.rest z.rest
  rw [← List.append_nil (setOne aOne)]
  refine setOne_ok hw₇ (j := aOne) (by decide) (by decide) fun t w₈ k₈ v₈ R₈ => WP.block_nil ?_
  have zv : ∀ j < nArrs, num s₇.mem G.KB G.w j = 0 := fun j hj => by
    have := VG.Proof.Rsa.KeyWorkspace.val32_zero_part z.value (a := j * (G.w + 2)) (c := G.w) (by
      have := Nat.mul_le_mul_right (G.w + 2) (show j + 1 ≤ nArrs by omega_using [hj])
      rw [Nat.succ_mul] at this; omega_using [this])
    simpa only [arr, S, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  refine ⟨fun j hj => ?_, ?_, ?_⟩
  · show num t.mem G.KB G.w j = KU (fun _ => 0) aOne 1 j
    simp only [KU]
    by_cases e : j = aOne
    · subst e; rw [VG.Proof.Rsa.Arm.Keys.upd_self, v₈, zv _ (by decide)]
    · rw [VG.Proof.Rsa.Arm.Keys.upd_ne _ _ e, k₈.num (by simpa using Ne.symm e) (by simp)
        (hw₇.fit64 (allArrs_lt j hj)), zv _ (allArrs_lt j hj)]
  · rw [k₈.slot (by decide) (by simp)]
    show w32 s₇.mem _ 16 = G.w
    rw [z.outside.w32 (d := 16) (by simp only [hdr]; omega_using []) (by decide), m₆]
    show (s₁.mem.readW (off (State.addr G.KB) 16) 32).toNat = G.w
    rw [u₁.mem, Mem.readW_writeW_self32, show (G.ksState s).gpr .r9 = s.gpr .r9 from rfl, h.r9,
      BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega_using [wl])
  · exact (u₁.rest ..).trans (R₆.mono (by simp) |>.trans ((z.rest.mono (by simp)).trans (R₈.mono (by simp))))

end

end VG.Proof.Dsa.Arm.Gen

end

end


/-! # DSA parameter generation on ARMv7: p and `(p − 1) / q`

`pArith` (`pArith_vp`): from X and q in claims, by the division of X by q
in the key working space: `p − 1 = X − X mod 2q` (`pm1_eq`) in array `aPm1`,
`p` in `aP` and big-endian at `sPBE`, `(p − 1) / q` in `aE`.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.Proof.Mont VG.Proof.Rsa.Arm.Keys
open VG.Impl.Dsa.Arm.Generation
open VG.Impl.Rsa.Arm.Keys (hdr)
open VG.Proof.Rsa.Arm.Recover (VP)

/-- `X − X mod q`, less `q` for an odd quotient, is `X − X mod 2q`. -/
theorem pm1_eq (x q : Nat) :
    x - x % q - (if x / q % 2 = 0 then 0 else q) = 2 * q * (x / (2 * q)) := by
  have h1 := Nat.mod_add_div x q
  have h2 : x / (2 * q) = x / q / 2 := by rw [Nat.mul_comm, Nat.div_div_eq_div_mul]
  have h3 := Nat.mod_add_div (x / q) 2
  rw [h2]
  generalize x / q / 2 = a at h3 ⊢
  generalize x / q = b at h1 h3 ⊢
  have e : x - x % q = q * b := by omega_arith
  rw [e]
  have e2 : 2 * q * a = 2 * (q * a) := by rw [Nat.mul_assoc]
  rcases Nat.mod_two_eq_zero_or_one b with h | h
  · simp only [h, ↓reduceIte]
    have : b = 2 * a := by omega_arith
    rw [this, Nat.mul_left_comm, e2]; omega_arith
  · simp only [show ¬ b % 2 = 0 by omega_arith, ↓reduceIte]
    have : b = 2 * a + 1 := by omega_arith
    rw [this, Nat.mul_add, Nat.mul_one, Nat.mul_left_comm, e2]; omega_arith

/-- The certificates of `pArith`'s pieces that depend on the geometry. -/
structure PArithCerts (L Lq : Nat) : Prop where
  st : Cert7 (storeBE L aP sPBE L)

theorem pArithCerts_128 : PArithCerts 128 20 :=
  ⟨⟨VG.Taint.hintOfSize VG.Arm.taint 4096 (Taint.ofRegs [.r7, .r8, .r9]) (storeBE 128 aP sPBE 128), by kernel_rfl⟩⟩

theorem pArithCerts_256 : PArithCerts 256 32 :=
  ⟨⟨VG.Taint.hintOfSize VG.Arm.taint 4096 (Taint.ofRegs [.r7, .r8, .r9]) (storeBE 256 aP sPBE 256), by kernel_rfl⟩⟩

theorem pArithCerts_384 : PArithCerts 384 32 :=
  ⟨⟨VG.Taint.hintOfSize VG.Arm.taint 4096 (Taint.ofRegs [.r7, .r8, .r9]) (storeBE 384 aP sPBE 384), by kernel_rfl⟩⟩

/-- The candidate p from X and q. -/
abbrev pVal (x q : Nat) : Nat := x + 1 - x % (2 * q)

/-- The arrays after `pArith`. -/
abbrev pA (x q : Nat) : Nat → Nat :=
  KU (KU (KU (KU (fun _ => 0) aOne 1) aPm1 (pVal x q - 1)) aE ((pVal x q - 1) / q)) aP (pVal x q)

/-- The stage after `pArith`. -/
abbrev pOut (c : Cfg) (G : GP) (x q : Nat) (rest : Claims) : Cfg :=
  { c with
    cl := (sPBE, Spec.Rsa.i2osp (pVal x q) G.pLen) :: rest
    A := pA x q
    live := [aP, aE, aPm1, aOne]
    kls := [] }

/-- Simplifies the arrays' values of a stage. -/
macro "arr_simp" : tactic => `(tactic| simp only [KU, VG.Proof.Rsa.Arm.Keys.upd, divCfg, A0, aQt, aRm, aDv, aDt,
  aX, aT, aS, aPm1, aP, aE, aH, aOne, aG, aZero, aTmp, slOdd, Nat.reduceEqDiff, ↓reduceIte])

/-- The arrays after the loads, the division and `p − 1`. -/
abbrev aL (x q : Nat) : Nat → Nat := KU (KU (KU A0 aQt x) aX x) aDv q
abbrev aD (x q : Nat) : Nat → Nat := KU (KU (aL x q) aQt (x / q)) aRm (x % q)
abbrev aM (x q : Nat) : Nat → Nat :=
  KU (KU (KU (fun _ => 0) aOne 1) aQt (x / q)) aPm1 (x - x % q - (if x / q % 2 = 0 then 0 else q))

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- The stages after the loads, the division and `p − 1`. -/
abbrev cL (c : Cfg) (G : GP) (x q : Nat) : Cfg :=
  { c with A := aL x q, live := [aDv, aX, aQt, aOne, aZero], KV := KU c.KV 16 G.w, kls := [16] }
abbrev cD (c : Cfg) (G : GP) (x q : Nat) : Cfg :=
  { c with A := aD x q, live := [aQt, aRm, aDv, aX, aOne, aZero], KV := KU c.KV 16 G.w, kls := [16] }
abbrev cM (c : Cfg) (x q : Nat) : Cfg := { c with A := aM x q, live := [aPm1, aQt, aOne], kls := [] }

theorem pLoads_vp {xb qb : List Byte}
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hx : (sX, xb) ∈ c.cl) (hxl : xb.length = G.pLen) (hqc : (sQ, qb) ∈ c.cl) (hql : qb.length = G.qLen) :
    VP (St G c X) (VG.Impl.Rsa.Arm.Keys.seqs [ksSetup, loadS G.pLen aQt sX G.pLen, loadS G.pLen aX sX G.pLen,
        loadS G.pLen aDv sQ G.qLen])
      (fun σ s => St G (cL c G (Spec.Dsa.decodeBE xb) (Spec.Dsa.decodeBE qb)) X σ s ∧ Top G s.mem aDv) := by
  have w1 : 4 * G.w = G.pLen := by simp only [GP.w]; omega_arith
  refine VP.seq (G := St G { c with A := A0, live := [aOne, aZero], KV := KU c.KV 16 G.w, kls := [16] } X)
    ((ksSetup_vp (G := G) (c := c) (X := X)).mono (fun _ _ h => h) fun σ s ⟨h, x⟩ =>
      ⟨h.mono (fun o ho => ⟨ho, rfl⟩) (fun y hy => hy) (fun j hj => ⟨by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; rcases hj with rfl | rfl <;> decide, rfl⟩)
        (fun d hd => ⟨hd, rfl⟩), x⟩) ?_
  refine VP.seq ((loadS_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r4, .r6, .r7, .r8, .r9])
    (VG.Impl.Rsa.Arm.CrtValues.load aQt), by kernel_rfl⟩ rfl (by decide) (by exact hx) hxl (by omega_arith) (by omega_arith)).mono
    (fun _ _ h => h) fun _ _ h => h.1) ?_
  refine VP.seq ((loadS_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r4, .r6, .r7, .r8, .r9])
    (VG.Impl.Rsa.Arm.CrtValues.load aX), by kernel_rfl⟩ rfl (by decide) (by exact hx) hxl (by omega_arith) (by omega_arith)).mono
    (fun _ _ h => h) fun _ _ h => h.1) ?_
  exact loadS_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r4, .r6, .r7, .r8, .r9])
    (VG.Impl.Rsa.Arm.CrtValues.load aDv), by kernel_rfl⟩ rfl (by decide) (by exact hqc) hql (by omega_arith) (by omega_arith)

theorem pDivide_vp {x q : Nat} (hpos : 0 < q)
    (hlq : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384) :
    VP (fun σ s => St G (cL c G x q) X σ s ∧ Top G s.mem aDv)
      (VG.Impl.Rsa.Arm.Keys.seqs [.block (VG.Impl.Rsa.Arm.CrtValues.divHdr aQt aRm aDv aDt), VG.Impl.Rsa.Arm.Div.code,
        .block (wRegs G.pLen)])
      (St G (cD c G x q) X) := by
  refine VP.seq (divHdr_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9])
    (.block (VG.Impl.Rsa.Arm.CrtValues.divHdr aQt aRm aDv aDt)), by kernel_rfl⟩ (by decide) (by decide) (by decide)
    (by decide) (by simp) (by arr_simp) (by simp)) ?_
  refine VP.seq (div_vp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp; decide) (by arr_simp; exact hpos)) ?_
  refine (wRegs_vp rfl hlq).mono (fun _ _ h => h) fun σ s ⟨h, x⟩ => ⟨h.mono (fun o ho => ⟨ho, rfl⟩)
    (fun y hy => hy) (fun j hj => ?_) (fun d hd => ⟨hd, rfl⟩), x⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by arr_simp⟩

theorem pPm1_vp {x q : Nat} :
    VP (St G (cD c G x q) X)
      (VG.Impl.Rsa.Arm.Keys.seqs [VG.Impl.Rsa.Arm.Keys.sub3 aT aX aRm, .block (VG.Impl.Rsa.Arm.Keys.bitOf slOdd aQt),
        VG.Impl.Rsa.Arm.Keys.sel aS aZero aDv slOdd, VG.Impl.Rsa.Arm.Keys.sub3 aPm1 aT aS])
      (St G (cM c x q) X) := by
  refine VP.seq (sub3_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9])
    (VG.Impl.Rsa.Arm.Keys.sub3 aT aX aRm), by kernel_rfl⟩ (by decide) (by simp) (by simp) (by decide) (by decide)
    (by arr_simp; exact Nat.mod_le _ _)) ?_
  refine VP.seq (bitOf_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9])
    (.block (VG.Impl.Rsa.Arm.Keys.bitOf slOdd aQt)), by kernel_rfl⟩ (by simp) (by decide)) ?_
  refine VP.seq (sel_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9])
    (VG.Impl.Rsa.Arm.Keys.sel aS aZero aDv slOdd), by kernel_rfl⟩ (by decide) (by simp) (by simp) (by decide) (by decide)
    (by simp) (by arr_simp; exact Nat.le_of_lt_succ (Nat.mod_lt _ (by decide)))) ?_
  refine (sub3_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9])
    (VG.Impl.Rsa.Arm.Keys.sub3 aPm1 aT aS), by kernel_rfl⟩ (by decide) (by simp) (by simp) (by decide) (by decide)
    (by
      arr_simp
      split
      · exact Nat.zero_le _
      · rename_i hne
        have h1 := Nat.mod_add_div x q
        have h2 : 1 ≤ x / q := Nat.pos_of_ne_zero fun e => hne (by rw [e])
        have h3 := Nat.mul_le_mul_left q h2
        omega_arith)).mono (fun _ _ h => h) fun σ s ⟨h, xx⟩ => ⟨h.mono (fun o ho => ⟨ho, rfl⟩)
      (fun y hy => hy) (fun j hj => ?_) (fun d hd => absurd hd (by simp)), xx⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl <;> exact ⟨by simp, by arr_simp⟩

theorem pVal_eq (x q : Nat) : pVal x q = 2 * q * (x / (2 * q)) + 1 := VG.Proof.Dsa.Generation.pReduction_quotient x q

theorem pVal_lt {x q K : Nat} (hK : 1 ≤ K) (hx : x < 2 ^ K) : pVal x q < 2 ^ K := by
  have le : 2 * q * (x / (2 * q)) ≤ x := Nat.mul_div_le x (2 * q)
  have odd : pVal x q % 2 = 1 := VG.Proof.Dsa.Generation.pReduction_odd x q
  have ev : 2 ^ K % 2 = 0 := by
    rw [show K = K - 1 + 1 by omega_arith, Nat.pow_succ]; simp
  rw [pVal_eq] at odd ⊢
  rcases Nat.lt_or_ge (2 * q * (x / (2 * q)) + 1) (2 ^ K) with h | h
  · exact h
  · have : 2 * q * (x / (2 * q)) + 1 = 2 ^ K := by omega_arith
    rw [this] at odd; omega_arith

theorem pTail_vp {x q : Nat} (cert : Cert7 (storeBE G.pLen aP sPBE G.pLen)) (hq : 0 < q)
    (hlq : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384) (hx : x < 2 ^ (8 * G.pLen)) {rest : Claims}
    (hrest : ∀ y ∈ rest, y ∈ c.cl ∧ Apart sPBE G.pLen y) :
    VP (St G (cM c x q) X)
      (VG.Impl.Rsa.Arm.Keys.seqs [VG.Impl.Rsa.Arm.Keys.copy aP aPm1, .block (VG.Impl.Rsa.Arm.Keys.orOne aP),
        VG.Impl.Rsa.Arm.Keys.copy aE aQt, .block (VG.Impl.Rsa.Arm.Keys.clrLow aE), storeBE G.pLen aP sPBE G.pLen])
      (St G (pOut c G x q rest) X) := by
  have w1 : 4 * G.w = G.pLen := by simp only [GP.w]; omega_arith
  have pm := pm1_eq x q
  have pv := pVal_eq x q
  have plt := pVal_lt (q := q) (by omega_arith) hx
  have hP : 2 * ((x - x % q - (if x / q % 2 = 0 then 0 else q)) / 2) + 1 = pVal x q := by
    rw [pm, pv, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide)]
  have hE : 2 * (x / q / 2) = (pVal x q - 1) / q := by
    rw [VG.Proof.Dsa.Generation.pReduction_generatorExponent x hq, Nat.div_div_eq_div_mul, Nat.mul_comm q 2]
  have hM : x - x % q - (if x / q % 2 = 0 then 0 else q) = pVal x q - 1 := by rw [pm, pv]; omega_arith
  refine VP.seq (copy_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9])
    (VG.Impl.Rsa.Arm.Keys.copy aP aPm1), by kernel_rfl⟩ (by decide) (by simp) (by decide)) ?_
  refine VP.seq (orOne_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9])
    (.block (VG.Impl.Rsa.Arm.Keys.orOne aP)), by kernel_rfl⟩ (by simp)) ?_
  refine VP.seq (copy_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9])
    (VG.Impl.Rsa.Arm.Keys.copy aE aQt), by kernel_rfl⟩ (by decide) (by simp) (by decide)) ?_
  refine VP.seq (clrLow_vp ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r7, .r8, .r9])
    (.block (VG.Impl.Rsa.Arm.Keys.clrLow aE)), by kernel_rfl⟩ (by simp)) ?_
  refine (storeBE_vp cert rfl (by simp) (by omega_arith) (by omega_arith) (by simp only [sPBE, sK, sA, wa]; omega_arith)
    (cl' := rest) fun y hy => by exact hrest y hy).mono (fun _ _ h => h) fun σ s ⟨h, xx⟩ =>
      ⟨h.mono (fun o ho => ⟨ho, rfl⟩) (fun y hy => ?_) (fun j hj => ?_) (fun d hd => absurd hd (by simp)), xx⟩
  · rcases List.mem_cons.mp hy with rfl | hy
    · refine List.mem_cons.mpr (.inl ?_)
      arr_simp
      rw [hP, Nat.mod_eq_of_lt plt]
    · exact List.mem_cons_of_mem _ hy
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl <;> refine ⟨by simp, ?_⟩ <;> arr_simp
    · exact hP
    · exact hE
    · exact hM

/-- p and `(p − 1) / q` from X and q. -/
theorem pArith_vp {xb qb : List Byte} (certs : PArithCerts G.pLen G.qLen)
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hx : (sX, xb) ∈ c.cl) (hxl : xb.length = G.pLen) (hqc : (sQ, qb) ∈ c.cl) (hql : qb.length = G.qLen)
    (hpos : 0 < Spec.Dsa.decodeBE qb) {rest : Claims} (hrest : ∀ y ∈ rest, y ∈ c.cl ∧ Apart sPBE G.pLen y) :
    VP (St G c X) (pArith G.pLen G.qLen)
      (St G (pOut c G (Spec.Dsa.decodeBE xb) (Spec.Dsa.decodeBE qb) rest) X) := by
  have hxlt : Spec.Dsa.decodeBE xb < 2 ^ (8 * G.pLen) := by
    have := VG.Proof.Dsa.decodeBE_lt xb
    rwa [hxl, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
  exact VP.seq (pLoads_vp hlq hx hxl hqc hql) (VP.seq (pDivide_vp hpos (by omega_arith))
    (VP.seq pPm1_vp (pTail_vp certs.st hpos (by omega_arith) hxlt hrest)))

end

end VG.Proof.Dsa.Arm.Gen

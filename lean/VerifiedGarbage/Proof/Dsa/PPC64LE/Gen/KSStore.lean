module

public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Rsa.PPC64LE.CvBytes
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Framework.Inline
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyHalf
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Test
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Bytes
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs
public import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyOps
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyBits

/-! ### `Dsa.PPC64LE.Gen.KSLoad`, which this module and modules that import it used -/

section

/-! ### `Dsa.PPC64LE.Gen.KSSetup`, which this module and modules that import it used -/

section

/-! ### `Dsa.PPC64LE.Gen.KSOps`, which this module and modules that import it used -/

section

/-! ### `Dsa.PPC64LE.Gen.KS`, which only this module used -/

section

/-! # DSA parameter generation on PPC64LE: steps in the key working space

The operations on the arrays of the key working space
(`Impl/Rsa/PPC64LE/KeyWs.lean`) are proven (`Proof/Rsa/PPC64LE/KeyOps.lean`,
…) on a state whose one writable region is the working space, with its
registers set (`Ws`). `SS.ksWP` runs such code from a state of the search,
narrowed to the working space (`SS.ws`, given the registers `KR`), and
`SS.of_ks` is the state after it: what the step wrote of the arrays and
header words, everything else as it was.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Rsa.KeyWorkspace
open VG.Proof.Rsa.PPC64LE.Keys (Ws)
open VG.Impl.Dsa.PPC64LE.Generation

/-- The state narrowed to the key working space. -/
abbrev GP.ksState (G : GP) (s : State) : State := s.withRegions s.rd [G.rK]

/-- The key working space's registers: its digits, its stride and its base. -/
structure KR (G : GP) (s : State) : Prop where
  r29 : s.gpr .r29 = BitVec.ofNat 64 G.w
  r30 : s.gpr .r30 = BitVec.ofNat 64 (S G.w)
  r31 : s.gpr .r31 = G.KB

theorem KR.of_keep {G : GP} {s t : State} {ws : List Reg} (h : KR G s) (k : Keep ws s t)
    (h29 : .r29 ∉ ws := by decide) (h30 : .r30 ∉ ws := by decide) (h31 : .r31 ∉ ws := by decide) : KR G t :=
  ⟨(k.gpr h29).trans h.r29, (k.gpr h30).trans h.r30, (k.gpr h31).trans h.r31⟩

section
variable {G : GP} {STK : Nat} {σ : State} {c : Cfg} {s : State}

theorem SS.kbNat (h : SS G STK σ c s) : G.KB.toNat = G.scr.toNat + kB G.pLen := by
  have := h.gi.wBig; have := h.gi.kBig; have := h.gi.scrFit
  have : 0 < kz G.pLen := by simp only [kz, hdr]; omega_using []
  rw [GP.KB, GP.sa, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show kB G.pLen < 2 ^ 64 by omega_arith),
    Nat.mod_eq_of_lt (by omega_arith)]

theorem SS.wsWith (h : SS G STK σ c s) (hr : KR G s) (rd : List Region) :
    Ws (s.withRegions rd [G.rK]) G.KB (kz G.pLen) G.w nArrs := by
  have := h.gi.wBig; have := h.gi.kBig; have := h.gi.scrFit
  have e := h.kbNat
  have l := h.lens
  refine ⟨VG.Proof.Bignum.PPC64LE.Scr.of_mem (List.mem_singleton_self _) (by show _ + kz G.pLen ≤ _; omega_arith),
    ?_, ?_, ?_, hr.r29, hr.r30, hr.r31⟩ <;>
    simp only [arr, S, hdr, nArrs, kz, GP.w] <;> rcases l with e | e | e <;> rw [e] <;> decide

theorem SS.ws (h : SS G STK σ c s) (hr : KR G s) : Ws (G.ksState s) G.KB (kz G.pLen) G.w nArrs := h.wsWith hr s.rd

/-- The narrowed state's regions are within the state's. -/
theorem SS.kcov (h : SS G STK σ c s) : Covers (s.rd ++ [G.rK]) (s.rd ++ s.wr) ∧ Covers [G.rK] s.wr := by
  have inS : G.rScr ∈ s.wr := by rw [h.gi.wr, h.gi.pre.wr, h.gi.hG]; simp
  have big := h.gi.wBig; have kb := h.gi.kBig
  have hw : Covers [G.rK] s.wr := (Covers.of_sub (rs' := [G.rScr]) fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨G.rScr, List.mem_singleton_self _, kB G.pLen, rfl, by show kB G.pLen + kz G.pLen ≤ G.scrLen * 8; omega_using [big, kb]⟩).trans
    (Covers.of_mem fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact inS)
  exact ⟨Covers.append (Covers.refl _) hw, hw⟩

/-- Code in the key working space alone, from a state of the search. -/
theorem SS.ksWP (h : SS G STK σ c s) {code : Prog isa} (hn : code.noCalls = true) {P : State → Prop}
    (hwp : WP isa code (G.ksState s) P) {Q : State → Prop}
    (k : ∀ t, P (G.ksState t) → t.rd = s.rd → t.wr = s.wr → Frame [G.rK] s.mem t.mem → Q t) :
    WP isa code s Q := by
  refine regionModel.wp_narrow (r := s.rd) (w := [G.rK]) hwp h.kcov.1 h.kcov.2
    (Code.noFrames_of_noCalls hn) (.inl hn) fun t s' _ hr hw' f p => ?_
  have hr' : s'.rd = s.rd := hr
  refine k s' ?_ hr' hw' f
  show P (s'.withRegions s'.rd _)
  rw [hr']; exact p

/-- After a step in the key working space: its arrays and header words. -/
theorem SS.of_ks (h : SS G STK σ c s) {t : State} {ws : List Reg} (r : Keep ws s t) (sp : t.sp = s.sp)
    (f : Frame [G.rK] s.mem t.mem) {A : Nat → Nat} {live : List Nat} {KV : Nat → Nat} {kls : List Nat}
    (ha : Arrs t.mem G.KB G.w A live) (hl : ∀ j ∈ live, j < nArrs)
    (hk : ∀ d ∈ kls, slot t.mem G.KB d = KV d) (hko : ∀ d ∈ kls, KlsOk d) (h28 : .r28 ∉ ws := by decide) :
    SS G STK σ { c with A := A, live := live, KV := KV, kls := kls } t := by
  have gi := h.gi
  have big := gi.wBig
  have kb := gi.kBig
  have hE : hEnd ≤ kB G.pLen := by rcases gi.lens3 with e | e | e <;> rw [e] <;> decide
  refine ⟨gi.of_scr r sp (o := kB G.pLen) (n := kz G.pLen) hE (by omega_using [big, kb]) (f.mono (by simp)) h28,
    h.sb.frame f (fun x hx r hr => ?_) (fun x hx => ?_), h.clOk, ha, hl, hk, hko⟩
  · rw [List.mem_singleton] at hr; subst hr
    have := h.clOk x hx
    exact (gi.kdisj this.2.1 this.2.2).symm
  · have := (h.clOk x hx).2.2; have := gi.scrFit; omega_arith

/-- After an operation that writes the array `o` (to `v`) and no header word. -/
theorem SS.of_op (h : SS G STK σ c s) {t : State} {ws : List Reg} (r : Keep ws s t) (sp : t.sp = s.sp)
    (f : Frame [G.rK] s.mem t.mem) {o v : Nat} (ho : o < nArrs) (kp : Keep G.KB G.w [o] [] s.mem t.mem)
    (e : num t.mem G.KB G.w o = v) (h28 : .r28 ∉ ws := by decide) :
    SS G STK σ { c with A := VG.Proof.Rsa.KeyWorkspace.upd c.A o v, live := o :: c.live } t := by
  have l := h.lens
  refine h.of_ks r sp f (fun j hj => ?_) (fun j hj => ?_) (fun d hd => ?_) h.kslOk h28
  · by_cases hjo : j = o
    · subst hjo; rw [VG.Proof.Rsa.KeyWorkspace.upd_self]; exact e
    · rw [VG.Proof.Rsa.KeyWorkspace.upd_ne _ _ hjo, kp.num (by simpa using fun e => hjo e.symm) (by simp)
        (by have := arrs_fit l (h.liveOk j ((List.mem_cons.mp hj).resolve_left hjo)); have := kz_eq l
            show arr (G.pLen / 4) j + 4 * (G.pLen / 4 + 2) ≤ 2 ^ 64; omega_arith)]
      exact h.arrs j ((List.mem_cons.mp hj).resolve_left hjo)
  · rcases List.mem_cons.mp hj with rfl | hj
    · exact ho
    · exact h.liveOk j hj
  · rw [kp.slot (h.kslOk d hd).1 (by simp)]; exact h.ksl d hd

/-- After an operation that writes the header word `d` (to `v`) and no array. -/
theorem SS.of_opS (h : SS G STK σ c s) {t : State} {ws : List Reg} (r : Keep ws s t) (sp : t.sp = s.sp)
    (f : Frame [G.rK] s.mem t.mem) {d v : Nat} (hd : KlsOk d) (kp : Keep G.KB G.w [] [d] s.mem t.mem)
    (e : slot t.mem G.KB d = v) (h28 : .r28 ∉ ws := by decide) :
    SS G STK σ { c with KV := VG.Proof.Rsa.KeyWorkspace.upd c.KV d v, kls := d :: c.kls } t := by
  have l := h.lens
  refine h.of_ks r sp f (fun j hj => ?_) h.liveOk (fun e' he => ?_) (fun e' he => ?_) h28
  · rw [kp.num (by simp) (by simpa using hd.1)
      (by have := arrs_fit l (h.liveOk j hj); have := kz_eq l
          show arr (G.pLen / 4) j + 4 * (G.pLen / 4 + 2) ≤ 2 ^ 64; omega_arith)]
    exact h.arrs j hj
  · by_cases hed : e' = d
    · subst hed; rw [VG.Proof.Rsa.KeyWorkspace.upd_self]; exact e
    · rcases List.mem_cons.mp he with rfl | he
      · exact absurd rfl hed
      rw [VG.Proof.Rsa.KeyWorkspace.upd_ne _ _ hed, kp.slot (h.kslOk e' he).1 (by
        simp only [List.mem_singleton, forall_eq]
        have := h.kslOk e' he; have := hd; simp only [KlsOk] at *; omega_arith)]
      exact h.ksl e' he
  · rcases List.mem_cons.mp he with rfl | he
    · exact hd
    · exact h.kslOk e' he

end

end VG.Proof.Dsa.PPC64LE.Gen

end

end


/-! # DSA parameter generation on PPC64LE: the operations on the key working space as pieces

A stage of the arithmetic (`KSt`) is a stage of the search with the key
working space's registers set (`KR`). Each operation of
`Proof/Rsa/PPC64LE/KeyOps.lean` and `KeyBits.lean` from it, as a piece
(`ks_vp`): the taint analysis takes `r28`–`r31` public.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE VG.Proof.Mont
open VG.Proof.Rsa.KeyWorkspace (S arr num slot Arrs)
open VG.Proof.Rsa.PPC64LE.Keys (Ws opRegs sub3_ok sel_ok copy_ok bitOf_ok orOne_ok clrLow_ok stBorrow_ok)
open VG.Impl.Rsa.PPC64LE.Keys (sub3 sel copy bitOf orOne clrLow stBorrow)
open VG.Impl.Dsa.PPC64LE.Generation

/-- `A` with `j ↦ v`. -/
abbrev KU := VG.Proof.Rsa.KeyWorkspace.upd

/-- The memory frame of the key operations. -/
abbrev KKeep := VG.Proof.Rsa.KeyWorkspace.Keep

/-- A stage of the arithmetic. -/
abbrev KSt (G : GP) (c : Cfg) (X : State → Prop) (σ s : State) : Prop := St G c X σ s ∧ KR G s

/-- The taint analysis of code in the key working space. -/
abbrev CertK (code : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r28, .r29, .r30, .r31]) code hc).isSome = true

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- An operation in the key working space, from a state of the search. -/
theorem SS.ksOp {STK : Nat} {σ s : State} (h : SS G STK σ c s) {code : Prog isa} (hn : code.noCalls = true)
    {js ds : List Nat} {P : State → Prop} {ws : List Reg}
    (hwp : WP isa code (G.ksState s) fun t => Ws t G.KB (kz G.pLen) G.w nArrs ∧
      KKeep G.KB G.w js ds s.mem t.mem ∧ P t ∧ VG.Proof.Bignum.PPC64LE.Keep ws (G.ksState s) t) {Q : State → Prop}
    (k : ∀ t, KKeep G.KB G.w js ds s.mem t.mem → P (G.ksState t) → Keep ws s t → t.sp = s.sp →
      Frame [G.rK] s.mem t.mem → Q t) :
    WP isa code s Q :=
  h.ksWP hn hwp fun t ⟨_, kp, p, r⟩ hr hw f => k t kp p ⟨r.gpr, hr, hw⟩ r.sp f

/-- A piece in the key working space. -/
theorem ks_vp {F Q : State → State → Prop} {cf : State → Cfg} {code : Prog isa} (cert : CertK code)
    (hF : ∀ σ s, F σ s → SS G 176 σ (cf σ) s ∧ KR G s) (wp : ∀ σ s, F σ s → WP isa code s (Q σ)) : VP F code Q :=
  VP.pub (G := G) (fun σ s hs => ⟨(hF σ s hs).1.gi.r28, by rw [(hF σ s hs).1.gi.sp, ← (hF σ s hs).1.gi.hG]; rfl⟩)
    [.r29, .r30, .r31] cert (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
      have a := (hF _ _ h₁).2; have b := (hF _ _ h₂).2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a.r29, b.r29]
      · rw [a.r30, b.r30]
      · rw [a.r31, b.r31]) wp

/-- `[o] := [a] − [b]`, for `[b] ≤ [a]`. -/
theorem sub3_vp {o a b : Nat} (cert : CertK (sub3 o a b)) (ho : o < nArrs) (ha : a ∈ c.live) (hb : b ∈ c.live)
    (hoa : o ≠ a) (hob : o ≠ b) (hle : c.A b ≤ c.A a) :
    VP (KSt G c X) (sub3 o a b) (KSt G { c with A := KU c.A o (c.A a - c.A b), live := o :: c.live } X) := by
  refine ks_vp cert (fun σ s h => ⟨h.1.1, h.2⟩) fun σ s ⟨⟨h, x⟩, kr⟩ => ?_
  have hw := h.ws kr
  have va := h.arrs.get ha
  have vb := h.arrs.get hb
  refine h.ksOp (P := fun t => num t.mem G.KB G.w o + num s.mem G.KB G.w b =
      num s.mem G.KB G.w a + 2 ^ (32 * G.w) * (t.gpr .r9).toNat ∧ (t.gpr .r9).toNat ≤ 1) rfl
    ((sub3_ok hw ho (h.liveOk a ha) (h.liveOk b hb) (by decide) hoa hob).mono fun t ⟨w, k, v, br, r⟩ => ⟨w, k, ⟨v, br⟩, r⟩)
    fun t k ⟨v, br⟩ R sp f => ⟨⟨h.of_op R sp f ho k ?_, x⟩, kr.of_keep R⟩
  simp only [GP.ksState, State.withRegions_mem, State.withRegions_gpr] at v br
  rw [va, vb] at v
  have lt : num t.mem G.KB G.w o < 2 ^ (32 * G.w) := val32_lt _ _ _ _
  have alt : c.A a < 2 ^ (32 * G.w) := va ▸ val32_lt _ _ _ _
  generalize 2 ^ (32 * G.w) = M at v lt alt
  rcases (by omega_using [br] : (t.gpr .r9).toNat = 0 ∨ (t.gpr .r9).toNat = 1) with e | e <;> rw [e] at v
  · omega_using [v]
  · have : M * 1 = M := Nat.mul_one M
    omega_using [hle, v, lt]

/-- `[o] := [b]` if the header word `sl` is 1, else `[a]`. -/
theorem sel_vp {o a b sl : Nat} (cert : CertK (sel o a b sl)) (ho : o < nArrs) (ha : a ∈ c.live) (hb : b ∈ c.live)
    (hoa : o ≠ a) (hob : o ≠ b) (hsl : sl ∈ c.kls) (bit : c.KV sl ≤ 1) :
    VP (KSt G c X) (sel o a b sl)
      (KSt G { c with A := KU c.A o (if c.KV sl = 0 then c.A a else c.A b), live := o :: c.live } X) := by
  refine ks_vp cert (fun σ s h => ⟨h.1.1, h.2⟩) fun σ s ⟨⟨h, x⟩, kr⟩ => ?_
  have hw := h.ws kr
  have va := h.arrs.get ha
  have vb := h.arrs.get hb
  have vs := h.ksl sl hsl
  refine h.ksOp (P := fun t => num t.mem G.KB G.w o =
      (if slot s.mem G.KB sl = 0 then num s.mem G.KB G.w a else num s.mem G.KB G.w b)) rfl
    ((sel_ok hw ho (h.liveOk a ha) (h.liveOk b hb) (by decide) hoa hob (h.kslOk sl hsl).1
      (by show slot s.mem G.KB sl ≤ 1; rw [vs]; exact bit)).mono fun t ⟨w, k, v, r⟩ => ⟨w, k, v, r⟩)
    fun t k v R sp f => ⟨⟨h.of_op R sp f ho k (by
      simp only [GP.ksState, State.withRegions_mem] at v; rw [v, va, vb, vs]), x⟩, kr.of_keep R⟩

/-- `[o] := [a]`. -/
theorem copy_vp {o a : Nat} (cert : CertK (copy o a)) (ho : o < nArrs) (ha : a ∈ c.live) (hoa : o ≠ a) :
    VP (KSt G c X) (copy o a) (KSt G { c with A := KU c.A o (c.A a), live := o :: c.live } X) := by
  refine ks_vp cert (fun σ s h => ⟨h.1.1, h.2⟩) fun σ s ⟨⟨h, x⟩, kr⟩ => ?_
  have hw := h.ws kr
  have va := h.arrs.get ha
  refine h.ksOp (P := fun t => num t.mem G.KB G.w o = num s.mem G.KB G.w a) rfl
    ((copy_ok hw ho (h.liveOk a ha) (by decide) hoa).mono fun t ⟨w, k, v, r, _⟩ => ⟨w, k, v, r⟩)
    fun t k v R sp f => ⟨⟨h.of_op R sp f ho k (by
      simp only [GP.ksState, State.withRegions_mem] at v; rw [v, va]), x⟩, kr.of_keep R⟩

/-- The header word `sl` := `[j]`'s low bit. -/
theorem bitOf_vp {sl j : Nat} (cert : CertK (.block (bitOf sl j))) (hj : j ∈ c.live) (hsl : KlsOk sl) :
    VP (KSt G c X) (.block (bitOf sl j)) (KSt G { c with KV := KU c.KV sl (c.A j % 2), kls := sl :: c.kls } X) := by
  refine ks_vp cert (fun σ s h => ⟨h.1.1, h.2⟩) fun σ s ⟨⟨h, x⟩, kr⟩ => ?_
  have hw := h.ws kr
  have va := h.arrs.get hj
  refine h.ksOp (js := []) (ds := [sl]) (P := fun t => slot t.mem G.KB sl = num s.mem G.KB G.w j % 2) rfl
    (by rw [← List.append_nil (bitOf sl j)]
        exact bitOf_ok hw (h.liveOk j hj) (by decide) hsl.1 fun t w k v r => WP.block_nil ⟨w, k, v, r⟩)
    fun t k v R sp f => ⟨⟨h.of_opS R sp f hsl k (by
      simp only [GP.ksState, State.withRegions_mem] at v; rw [v, va]), x⟩, kr.of_keep R⟩

/-- `[j]`'s low bit set. -/
theorem orOne_vp {j : Nat} (cert : CertK (.block (orOne j))) (hj : j ∈ c.live) :
    VP (KSt G c X) (.block (orOne j))
      (KSt G { c with A := KU c.A j (2 * (c.A j / 2) + 1), live := j :: c.live } X) := by
  refine ks_vp cert (fun σ s h => ⟨h.1.1, h.2⟩) fun σ s ⟨⟨h, x⟩, kr⟩ => ?_
  have hw := h.ws kr
  have va := h.arrs.get hj
  refine h.ksOp (js := [j]) (ds := [])
    (P := fun t => num t.mem G.KB G.w j = 2 * (num s.mem G.KB G.w j / 2) + 1) rfl
    (by rw [← List.append_nil (orOne j)]
        exact orOne_ok hw (h.liveOk j hj) (by decide) fun t w k v r => WP.block_nil ⟨w, k, v, r⟩)
    fun t k v R sp f => ⟨⟨h.of_op R sp f (h.liveOk j hj) k (by
      simp only [GP.ksState, State.withRegions_mem] at v; rw [v, va]), x⟩, kr.of_keep R⟩

/-- `[j]`'s low bit cleared. -/
theorem clrLow_vp {j : Nat} (cert : CertK (.block (clrLow j))) (hj : j ∈ c.live) :
    VP (KSt G c X) (.block (clrLow j))
      (KSt G { c with A := KU c.A j (2 * (c.A j / 2)), live := j :: c.live } X) := by
  refine ks_vp cert (fun σ s h => ⟨h.1.1, h.2⟩) fun σ s ⟨⟨h, x⟩, kr⟩ => ?_
  have hw := h.ws kr
  have va := h.arrs.get hj
  refine h.ksOp (js := [j]) (ds := []) (P := fun t => num t.mem G.KB G.w j = 2 * (num s.mem G.KB G.w j / 2)) rfl
    (by rw [← List.append_nil (clrLow j)]
        exact clrLow_ok hw (h.liveOk j hj) (by decide) fun t w k v r _ => WP.block_nil ⟨w, k, v, r⟩)
    fun t k v R sp f => ⟨⟨h.of_op R sp f (h.liveOk j hj) k (by
      simp only [GP.ksState, State.withRegions_mem] at v; rw [v, va]), x⟩, kr.of_keep R⟩

end

end VG.Proof.Dsa.PPC64LE.Gen

end

end

/-! # DSA parameter generation on PPC64LE: the key working space set up

`ksEnter_vp`: its registers (`ksRegs`); `ksSetup_vp`: every array zero but
`[aOne] = 1`, and the top word of every other array zero (`TopAll`), which
the division's divisor needs.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE VG.Proof.Mont
open VG.Proof.Rsa.KeyWorkspace (S arr num slot Arrs)
open VG.Proof.Rsa.PPC64LE.Keys (Ws opRegs zeroArrays_ok setOne_ok)
open VG.Impl.Rsa.PPC64LE.Keys (zeroArrays setOne stride)
open VG.Impl.Dsa.PPC64LE.Generation

/-- The arrays after the setup: all zero but `[aOne] = 1`. -/
abbrev A0 : Nat → Nat := KU (fun _ => 0) aOne 1

/-- Every array. -/
abbrev allArrs : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]

theorem allArrs_lt : ∀ j ∈ allArrs, j < nArrs := by decide

/-- The top word of every array but `aOne` is zero. -/
abbrev TopAll (G : GP) (m : Mem) : Prop := ∀ j < nArrs, j ≠ aOne → w32 m G.KB (arr G.w j + 4 * G.w) = 0

theorem ofNat_stride' (w : Nat) :
    (BitVec.ofNat 64 w + BitVec.ofNat 64 2) <<< 2 = BitVec.ofNat 64 (S w) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq]
  simp only [S]
  omega_using []

theorem ofNat_digits15 (w : Nat) (hw : w ≤ 256) :
    (BitVec.ofNat 64 nArrs * BitVec.ofNat 64 (S w)) >>> 2 = BitVec.ofNat 64 (nArrs * (w + 2)) := by
  rw [← BitVec.ofNat_mul]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  simp only [S, nArrs]
  rw [Nat.mod_eq_of_lt (show 15 * (4 * (w + 2)) < 2 ^ 64 by omega_using [hw]),
    Nat.mod_eq_of_lt (show 15 * (w + 2) < 2 ^ 64 by omega_using [hw])]
  omega_using []

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- The key working space's registers. -/
theorem ksEnter_vp : VP (St G c X) (.block (ksRegs G.pLen)) (KSt G c X) := by
  refine VP.pub (SS.pub (c := fun _ => c) fun σ s h => h.1) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
    (Taint.ofRegs [.r28]) (.block (ksRegs G.pLen)), by kernel_rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp))
    fun σ s ⟨h, x⟩ => ?_
  have l := h.lens
  have kb15 : kB G.pLen < 2 ^ 15 := by rcases l with e | e | e <;> rw [e] <;> decide
  have w15 : G.pLen / 4 < 2 ^ 15 := by rcases l with e | e | e <;> rw [e] <;> decide
  have hb : WP isa (.block (ksRegs G.pLen)) s fun u =>
      (u.gpr .r31 = G.KB ∧ u.gpr .r29 = BitVec.ofNat 64 G.w ∧ u.gpr .r30 = BitVec.ofNat 64 (S G.w) ∧
        u.mem = s.mem) ∧ VG.Proof.Bignum.PPC64LE.Keep [.r29, .r30, .r31] s u := by
    refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ (by rfl)
    simp only [ksRegs, stride, scr, List.cons_append, List.nil_append]
    prun [h.gi.r28, exec_addi (show Reg.r28 ≠ .r0 by decide) kb15, exec_li w15,
      exec_addi (show Reg.r29 ≠ .r0 by decide) (show 2 < 2 ^ 15 by decide), ofNat_stride']
  refine WP.mono hb fun u ⟨⟨a31, a29, a30, m⟩, k⟩ => ⟨⟨h.of_keep ⟨k.gpr, k.rd, k.wr⟩ m k.sp, x⟩, a29, a30, a31⟩

/-- Every array zeroed, then `[aOne] = 1`. -/
theorem ksSetup_vp :
    VP (KSt G c X) ksSetup (fun σ t => KSt G { c with A := A0, live := allArrs } X σ t ∧ TopAll G t.mem) := by
  refine ks_vp ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31]) ksSetup, by kernel_rfl⟩
    (fun σ s h => ⟨h.1.1, h.2⟩) fun σ s ⟨⟨h, x⟩, kr⟩ => ?_
  have hw := h.ws kr
  have l := h.lens
  have nw := hw.nowrap
  have wl : G.w ≤ 96 := by simp only [GP.w]; rcases l with e | e | e <;> rw [e] <;> decide
  have w1 : 1 ≤ G.w := by simp only [GP.w]; rcases l with e | e | e <;> rw [e] <;> decide
  have fits : 160 + 4 * (nArrs * (G.w + 2)) ≤ kz G.pLen := by
    simp only [VG.Proof.Rsa.KeyWorkspace.hdr, nArrs, kz, GP.w, S]; omega_using []
  refine h.ksWP rfl (P := fun t => (∀ j < nArrs, num t.mem G.KB G.w j = A0 j) ∧ TopAll G t.mem ∧
      (∀ d, d + 4 ≤ 160 → slot t.mem G.KB d = slot s.mem G.KB d) ∧
      VG.Proof.Bignum.PPC64LE.Keep (.r8 :: opRegs) (G.ksState s) t) ?_
    fun t ⟨a, top, sl, R⟩ hr hw' f => ⟨⟨⟨?_, x⟩, kr.of_keep (show Keep (.r8 :: opRegs) s t from ⟨R.gpr, hr, hw'⟩)⟩,
      by simpa only [GP.ksState, State.withRegions_mem] using top⟩
  swap
  · refine h.of_ks (show Keep (.r8 :: opRegs) s t from ⟨R.gpr, hr, hw'⟩) R.sp f (fun j hj => a j (allArrs_lt j hj))
      allArrs_lt (fun d hd => ?_) h.kslOk
    rw [show slot t.mem G.KB d = slot (G.ksState t).mem G.KB d from rfl, sl d (by
      have := (h.kslOk d hd).1; simp only [VG.Proof.Rsa.KeyWorkspace.hdr] at this; omega_using [this])]
    exact h.ksl d hd
  unfold ksSetup
  rw [WP.seq_iff]
  have hb : WP isa (.block [.li .r8 nArrs, .mul .r8 .r8 .r30, .lsr .d .r8 .r8 2]) (G.ksState s) fun u =>
      (u.gpr .r8 = BitVec.ofNat 64 (nArrs * (G.w + 2)) ∧ u.mem = s.mem) ∧
        VG.Proof.Bignum.PPC64LE.Keep [.r8] (G.ksState s) u := by
    refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ (by decide)
    prun [hw.r30, exec_li (show nArrs < 2 ^ 15 by decide), ofNat_digits15 G.w (by omega_using [wl])]
    rfl
  refine WP.mono hb fun u ⟨⟨u8, um⟩, ku⟩ => ?_
  have hu : Ws u G.KB (kz G.pLen) G.w nArrs := hw.of_keep ku
  rw [WP.seq_iff]
  refine WP.mono (zeroArrays_ok hu u8 (by simp only [nArrs]; omega_using []) (by simp only [nArrs]; omega_using [wl]) fits)
    fun t₁ ⟨ht₁, z, out, kt⟩ => ?_
  rw [← List.append_nil (setOne aOne)]
  refine setOne_ok ht₁ (j := aOne) (by decide) (by decide) fun t ht k₈ v₈ R₈ => WP.block_nil ?_
  have zw : ∀ j < nArrs, ∀ i < G.w + 2, w32 t₁.mem G.KB (arr G.w j + 4 * i) = 0 := fun j hj i hi => by
    have hb : j * (G.w + 2) + i < nArrs * (G.w + 2) := by
      have := Nat.mul_le_mul_right (G.w + 2) (show j + 1 ≤ nArrs by omega_using [hj])
      rw [Nat.add_mul, Nat.one_mul] at this; omega_using [hi, this]
    have := z (j * (G.w + 2) + i) hb
    rw [show 160 + 4 * (j * (G.w + 2) + i) = arr G.w j + 4 * i by
      simp only [arr, S, VG.Proof.Rsa.KeyWorkspace.hdr]; grind] at this
    exact this
  have zv : ∀ j < nArrs, num t₁.mem G.KB G.w j = 0 := fun j hj =>
    VG.Proof.Bignum.PPC64LE.val32_zero fun i hi => zw j hj i (by omega_using [hi])
  refine ⟨fun j hj => ?_, fun j hj hne => ?_, fun d hd => ?_, ?_⟩
  · show num _ _ _ _ = VG.Proof.Rsa.KeyWorkspace.upd (fun _ => 0) aOne 1 j
    by_cases e : j = aOne
    · subst e; rw [VG.Proof.Rsa.KeyWorkspace.upd_self, v₈, zv _ (by decide)]
    · rw [VG.Proof.Rsa.KeyWorkspace.upd_ne _ _ e, k₈.num (by simpa using Ne.symm e) (by simp)
        (ht.fit64 hj), zv _ hj]
  · rw [k₈.word (j := j) (i := G.w) (by simp only [S]; omega_using []) (by simpa using Ne.symm hne) (by simp) (ht.fit64 hj)]
    exact zw j hj G.w (by omega_using [])
  · rw [k₈.slot (by simp only [VG.Proof.Rsa.KeyWorkspace.hdr]; omega_using [hd]) (by simp)]
    show w32 t₁.mem G.KB d = w32 s.mem G.KB d
    rw [← um]
    exact out.w32 (.inl hd) (by omega_using [hd])
  · exact (ku.trans (kt.trans R₈)).mono (by simp)

end

end VG.Proof.Dsa.PPC64LE.Gen

end

end

/-! # DSA parameter generation on PPC64LE: numbers into the key working space

`loadAt_vp`: array `j`, zero, := the `n` big-endian bytes at `r6`
(`r8 = n`), readable and apart from the key working space (`load_ok`);
`loadS_vp`: from a claim on `scratch`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE VG.Proof.Mont
open VG.Proof.Rsa.KeyWorkspace (S arr num slot Arrs)
open VG.Proof.Rsa.PPC64LE.Keys (Ws load_ok)
open VG.Impl.Dsa.PPC64LE.Generation

section
variable {G : GP} {STK : Nat} {σ : State} {c : Cfg} {s : State}

/-- Code in the key working space, also reading the regions `rs`. -/
theorem SS.ksWPr (h : SS G STK σ c s) {rs : List Region} (hrs : Covers rs (s.rd ++ s.wr)) {code : Prog isa}
    (hn : code.noCalls = true) {P : State → Prop} (hwp : WP isa code (s.withRegions (s.rd ++ rs) [G.rK]) P)
    {Q : State → Prop}
    (k : ∀ t, P (t.withRegions (s.rd ++ rs) [G.rK]) → t.rd = s.rd → t.wr = s.wr → Frame [G.rK] s.mem t.mem →
      Q t) :
    WP isa code s Q :=
  regionModel.wp_narrow (r := s.rd ++ rs) (w := [G.rK]) hwp
    (Covers.append_left (Covers.append_left (Covers.left (Covers.refl _)) hrs) h.kcov.2.right) h.kcov.2
    (Code.noFrames_of_noCalls hn) (.inl hn) fun _ s' _ hr hw' f p => k s' p hr hw' f

end

theorem past_of_disjoint' {B : Addr} {Z : Nat} {r : Region} (hd : r.Disjoint ⟨B, Z⟩) {a : Addr}
    (ha : r.Contains a 1) : Z ≤ (a - B).toNat := by
  have := hd a ha
  simp only [Region.Contains] at this
  omega_using [this]

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- The taint analysis of a load, its source and length public. -/
abbrev CertL (j : Nat) : Prop := ∃ hc, (VG.Taint.check VG.PPC64LE.taint
  (Taint.ofRegs [.r28, .r29, .r30, .r31, .r6, .r8]) (VG.Impl.Rsa.PPC64LE.CrtValues.load j) hc).isSome = true

/-- Array `j`, zero, := the `n` bytes `bs` at `r6` (`r8 = n`), readable and
apart from the key working space. -/
theorem loadAt_vp {j n : Nat} {P : Addr} {bs : List Byte} (cert : CertL j)
    (hj : j < nArrs) (hjl : j ∈ c.live) (hj0 : c.A j = 0) (hn0 : 0 < n) (hnw : n ≤ 4 * G.w)
    (hsrc : ∀ σ s, St G c X σ s → Covers [⟨P, n⟩] (s.rd ++ s.wr) ∧
      Region.Disjoint ⟨P, n⟩ G.rK ∧ Spec.Rsa.bytesAt s.mem P n = bs) :
    VP (fun σ s => (KSt G c X σ s ∧ TopAll G s.mem) ∧ s.gpr .r6 = P ∧ s.gpr .r8 = BitVec.ofNat 64 n)
      (VG.Impl.Rsa.PPC64LE.CrtValues.load j)
      (fun σ t => KSt G { c with A := KU c.A j (Spec.Dsa.decodeBE bs), live := j :: c.live } X σ t ∧
        TopAll G t.mem) := by
  refine VP.pub (G := G) (fun σ s hs => ⟨hs.1.1.1.1.gi.r28, by rw [hs.1.1.1.1.gi.sp, ← hs.1.1.1.1.gi.hG]; rfl⟩)
    [.r29, .r30, .r31, .r6, .r8] cert
    (fun σ₁ σ₂ s₁ s₂ ⟨⟨⟨_, a⟩, _⟩, a6, a8⟩ ⟨⟨⟨_, b⟩, _⟩, b6, b8⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [a.r29, b.r29]
      · rw [a.r30, b.r30]
      · rw [a.r31, b.r31]
      · rw [a6, b6]
      · rw [a8, b8]) fun σ s ⟨⟨⟨⟨h, x⟩, kr⟩, top⟩, p6, p8⟩ => ?_
  obtain ⟨hR, sep, b⟩ := hsrc σ s ⟨h, x⟩
  have l := h.lens
  have hw := h.wsWith kr (s.rd ++ [⟨P, n⟩])
  have nw := hw.nowrap
  have fa := hw.arr_fit hj
  have z : val32 s.mem G.KB (arr G.w j) G.w = 0 := by
    have := h.arrs.get hjl; rw [hj0] at this; exact this
  have w96 : G.w ≤ 96 := by simp only [GP.w]; rcases l with e | e | e <;> rw [e] <;> decide
  have hc : ∀ i < n, (⟨P, n⟩ : Region).Contains (P + BitVec.ofNat 64 i) 1 := fun i hi =>
    Offset.contains_base _ (by omega_using [hi]) (by omega_using [hnw, w96, hi])
  refine h.ksWPr hR rfl (P := fun t => Ws t G.KB (kz G.pLen) G.w nArrs ∧ KKeep G.KB G.w [j] [] s.mem t.mem ∧
      num t.mem G.KB G.w j = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P n) ∧
      VG.Proof.Bignum.PPC64LE.Keep [.r0, .r5, .r6, .r8] (s.withRegions (s.rd ++ [⟨P, n⟩]) [G.rK]) t ∧
      VG.Proof.Bignum.Outside G.KB (arr G.w j) (4 * G.w) s.mem t.mem) ?_ ?_
  · refine WP.mono (load_ok hw hj (by decide) p6 p8 hn0 hnw
      (fun i hi => ⟨⟨P, n⟩, List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _)), hc i hi⟩)
      (fun i hi x hx e => by subst e; exact absurd (past_of_disjoint' sep (hc i hi)) (Nat.not_le.mpr hx))
      fun p hp => by rw [← VG.Proof.Bignum.PPC64LE.off_add]; exact VG.Proof.Bignum.byte_zero_of_val32 z hp)
      fun t ⟨w, k, v, r, o⟩ => ⟨w, k, v, r, o⟩
  · intro t ⟨_, k, v, R, o⟩ hr hw' fK
    simp only [State.withRegions_mem] at v
    have vw : num t.mem G.KB G.w j = Spec.Dsa.decodeBE bs := by rw [v, b, VG.Proof.Dsa.decodeBE_os2ip]
    have R' : Keep [.r0, .r5, .r6, .r8] s t := ⟨R.gpr, hr, hw'⟩
    refine ⟨⟨⟨h.of_op R' R.sp fK hj k vw, x⟩, kr.of_keep R'⟩, fun i hi hne => ?_⟩
    simp only [State.withRegions_mem] at k o
    have fi := hw.arr_fit hi
    by_cases e : i = j
    · subst e
      rw [VG.Proof.Mont.Outside.w32 o (.inr (Nat.le_refl _)) (by have := hw.fit64 hi; simp only [S] at this; omega_using [this])]
      exact top i hi hne
    · rw [k.word (j := i) (i := G.w) (by simp only [S]; omega_using []) (by simpa using Ne.symm e) (by simp)
        (hw.fit64 hi)]
      exact top i hi hne

/-- `loadAt_vp` without the top words: array `j`, zero, := the `n` bytes `bs`
at `r6` (`r8 = n`). -/
theorem loadZ_vp {j n : Nat} {P : Addr} {bs : List Byte} (cert : CertL j)
    (hj : j < nArrs) (hjl : j ∈ c.live) (hj0 : c.A j = 0) (hn0 : 0 < n) (hnw : n ≤ 4 * G.w)
    (hsrc : ∀ σ s, St G c X σ s → Covers [⟨P, n⟩] (s.rd ++ s.wr) ∧
      Region.Disjoint ⟨P, n⟩ G.rK ∧ Spec.Rsa.bytesAt s.mem P n = bs) :
    VP (fun σ s => KSt G c X σ s ∧ s.gpr .r6 = P ∧ s.gpr .r8 = BitVec.ofNat 64 n)
      (VG.Impl.Rsa.PPC64LE.CrtValues.load j)
      (KSt G { c with A := KU c.A j (Spec.Dsa.decodeBE bs), live := j :: c.live } X) := by
  refine VP.pub (G := G) (fun σ s hs => ⟨hs.1.1.1.gi.r28, by rw [hs.1.1.1.gi.sp, ← hs.1.1.1.gi.hG]; rfl⟩)
    [.r29, .r30, .r31, .r6, .r8] cert
    (fun σ₁ σ₂ s₁ s₂ ⟨⟨_, a⟩, a6, a8⟩ ⟨⟨_, b⟩, b6, b8⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [a.r29, b.r29]
      · rw [a.r30, b.r30]
      · rw [a.r31, b.r31]
      · rw [a6, b6]
      · rw [a8, b8]) fun σ s ⟨⟨⟨h, x⟩, kr⟩, p6, p8⟩ => ?_
  obtain ⟨hR, sep, b⟩ := hsrc σ s ⟨h, x⟩
  have hw := h.wsWith kr (s.rd ++ [⟨P, n⟩])
  have z : val32 s.mem G.KB (arr G.w j) G.w = 0 := by
    have := h.arrs.get hjl; rw [hj0] at this; exact this
  have w96 : G.w ≤ 96 := by simp only [GP.w]; rcases h.lens with e | e | e <;> rw [e] <;> decide
  have hc : ∀ i < n, (⟨P, n⟩ : Region).Contains (P + BitVec.ofNat 64 i) 1 := fun i hi =>
    Offset.contains_base _ (by omega_using [hi]) (by omega_using [hnw, w96, hi])
  refine h.ksWPr hR rfl (P := fun t => Ws t G.KB (kz G.pLen) G.w nArrs ∧ KKeep G.KB G.w [j] [] s.mem t.mem ∧
      num t.mem G.KB G.w j = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P n) ∧
      VG.Proof.Bignum.PPC64LE.Keep [.r0, .r5, .r6, .r8] (s.withRegions (s.rd ++ [⟨P, n⟩]) [G.rK]) t) ?_ ?_
  · refine WP.mono (load_ok hw hj (by decide) p6 p8 hn0 hnw
      (fun i hi => ⟨⟨P, n⟩, List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _)), hc i hi⟩)
      (fun i hi x hx e => by subst e; exact absurd (past_of_disjoint' sep (hc i hi)) (Nat.not_le.mpr hx))
      fun p hp => by rw [← VG.Proof.Bignum.PPC64LE.off_add]; exact VG.Proof.Bignum.byte_zero_of_val32 z hp)
      fun t ⟨w, k, v, r, _⟩ => ⟨w, k, v, r⟩
  · intro t ⟨_, k, v, R⟩ hr hw' fK
    simp only [State.withRegions_mem] at v k
    have vw : num t.mem G.KB G.w j = Spec.Dsa.decodeBE bs := by rw [v, b, VG.Proof.Dsa.decodeBE_os2ip]
    have R' : Keep [.r0, .r5, .r6, .r8] s t := ⟨R.gpr, hr, hw'⟩
    exact ⟨⟨h.of_op R' R.sp fK hj k vw, x⟩, kr.of_keep R'⟩

/-- Array `j`, zero, := the bytes `bs` that a claim puts at byte `o` of `scratch`. -/
theorem loadS_vp {j o n : Nat} {bs : List Byte} (cert : CertL j)
    (hj : j < nArrs) (hjl : j ∈ c.live) (hj0 : c.A j = 0) (hbs : (o, bs) ∈ c.cl) (hn : bs.length = n)
    (hn0 : 0 < n) (hnw : n ≤ 4 * G.w) (ho : o < 2 ^ 15) (hn15 : n < 2 ^ 15) :
    VP (fun σ s => KSt G c X σ s ∧ TopAll G s.mem) (loadS j o n)
      (fun σ t => KSt G { c with A := KU c.A j (Spec.Dsa.decodeBE bs), live := j :: c.live } X σ t ∧
        TopAll G t.mem) := by
  refine VP.seq (G := fun σ s => (KSt G c X σ s ∧ TopAll G s.mem) ∧ s.gpr .r6 = G.sa o ∧
      s.gpr .r8 = BitVec.ofNat 64 n)
    (VP.pub (G := G) (fun σ s hs => ⟨hs.1.1.1.gi.r28, by rw [hs.1.1.1.gi.sp, ← hs.1.1.1.gi.hG]; rfl⟩) []
      ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28]) (.block [scr .r6 o, .li .r8 n]), rfl⟩
      (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨⟨⟨h, x⟩, kr⟩, top⟩ => ?_)
    (loadAt_vp cert hj hjl hj0 hn0 hnw fun σ s ⟨h, x⟩ => ?_)
  · refine WP.sp_eq ?_
    refine WP.wr (exec_addi (by decide) ho) fun s₁ u₁ sp₁ _ => ?_
    refine WP.wr (exec_li hn15) fun t u sp _ => WP.block_nil fun _ => ⟨⟨⟨⟨(h.of_upd u₁ sp₁ (by decide)).of_upd u sp
      (by decide), x⟩, (kr.of_keep (ws := [.r6]) ⟨fun r hr => u₁.other r (by simpa using hr), u₁.rd, u₁.wr⟩).of_keep
      (ws := [.r8]) ⟨fun r hr => u.other r (by simpa using hr), u.rd, u.wr⟩⟩, by rw [u.mem, u₁.mem]; exact top⟩, ?_, ?_⟩
    · rw [u.other _ (by decide), u₁.gpr, h.gi.r28]
    · rw [u.gpr]
  · have gi := h.gi
    have big := gi.wBig
    have kb := gi.kBig
    have fit := gi.scrFit
    have inS : G.rScr ∈ s.wr := by rw [gi.wr, gi.pre.wr, gi.hG]; simp
    have ok := h.clOk _ hbs
    simp only [ClOk, hn] at ok
    have b := h.sb _ hbs
    simp only [hn] at b
    refine ⟨(Covers.of_sub (rs' := [G.rScr]) fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact ⟨G.rScr, List.mem_singleton_self _, o, rfl, show o + n ≤ G.scrLen * 8 by omega_using [ok]⟩).trans
      (Covers.of_mem fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact List.mem_append_right _ inS),
      (gi.kdisj ok.2.1 ok.2.2).symm, b⟩

end

end VG.Proof.Dsa.PPC64LE.Gen

end

end

/-! # DSA parameter generation on PPC64LE: numbers out of the key working space

`storeS_vp`: the claim at byte `o` of `scratch` := `[j]`'s low `n` bytes,
big-endian (`storeBytes_ok`), run on the whole state, whose `scratch` holds
the key working space (`SS.wsFull`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE VG.Proof.Mont
open VG.Proof.Rsa.KeyWorkspace (S arr num slot Arrs)
open VG.Proof.Rsa.PPC64LE.Keys (Ws storeBytes_ok bytes_of_store)
open VG.Impl.Dsa.PPC64LE.Generation

section
variable {G : GP} {STK : Nat} {σ : State} {c : Cfg} {s : State}

/-- The key working space, within `scratch`, on the whole state. -/
theorem SS.wsFull (h : SS G STK σ c s) (hr : KR G s) : Ws s G.KB (kz G.pLen) G.w nArrs := by
  have := h.gi.wBig; have := h.gi.kBig; have := h.gi.scrFit
  have e := h.kbNat
  have l := h.lens
  have inS : G.rScr ∈ s.wr := by rw [h.gi.wr, h.gi.pre.wr, h.gi.hG]; simp
  refine ⟨⟨⟨G.scr, kB G.pLen, G.scrLen * 8, inS, rfl, by omega_arith, by omega_using [this]⟩, by omega_arith⟩,
    ?_, ?_, ?_, hr.r29, hr.r30, hr.r31⟩ <;>
    simp only [arr, S, VG.Proof.Rsa.KeyWorkspace.hdr, nArrs, kz, GP.w] <;> rcases l with e | e | e <;> rw [e] <;> decide

end

/-- Bytes outside `[O, O + L)` kept, as a frame. -/
theorem frame_of_outside {O : Addr} {L : Nat} {m m' : Mem} (h : VG.Proof.Bignum.Outside O 0 L m m') :
    Frame [⟨O, L⟩] m m' := fun x hx => h x (.inr (by
  have := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at this
  show 0 + L ≤ (x - O).toNat
  omega_using [this]))

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- The taint analysis of a store, its destination, length and mask public. -/
abbrev CertS (j : Nat) : Prop := ∃ hc, (VG.Taint.check VG.PPC64LE.taint
  (Taint.ofRegs [.r28, .r29, .r30, .r31, .r5, .r8, .r9]) (VG.Impl.Rsa.PPC64LE.CrtValues.storeBytes j) hc).isSome = true

/-- The claim at byte `o` of `scratch` := `[j]`'s low `n` bytes, big-endian. -/
theorem storeS_vp {j o n : Nat} (cert : CertS j) (hj : j ∈ c.live) (hn0 : 0 < n) (hnw : n ≤ 4 * G.w)
    (ho15 : o < 2 ^ 15) (hn15 : n < 2 ^ 15) (hoc : ∀ σ s, St G c X σ s → ClOk G (o, List.replicate n 0))
    {cl' : Claims} (hcl : ∀ x ∈ cl', x ∈ c.cl ∧ Apart o n x) :
    VP (KSt G c X) (storeS j o n)
      (KSt G { c with cl := (o, Spec.Rsa.i2osp (c.A j % 2 ^ (8 * n)) n) :: cl' } X) := by
  refine VP.seq (G := fun σ s => KSt G c X σ s ∧ s.gpr .r5 = G.sa o ∧ s.gpr .r8 = BitVec.ofNat 64 n ∧
      s.gpr .r9 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if true then 1 else 0))
    (VP.pub (G := G) (fun σ s hs => ⟨hs.1.1.gi.r28, by rw [hs.1.1.gi.sp, ← hs.1.1.gi.hG]; rfl⟩) []
      ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
        (.block [scr .r5 o, .li .r8 n, .li .r9 0, .subi .r9 .r9 1]), rfl⟩
      (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨⟨h, x⟩, kr⟩ => ?_) ?_
  · refine WP.sp_eq ?_
    refine WP.wr (exec_addi (by decide) ho15) fun s₁ u₁ sp₁ _ => ?_
    refine WP.wr (exec_li hn15) fun s₂ u₂ sp₂ _ => ?_
    refine WP.wr (exec_li (by decide)) fun s₃ u₃ sp₃ _ => ?_
    refine WP.wr (exec_subi (by decide) (by decide)) fun t u sp _ => WP.block_nil fun _ => ?_
    have K : Keep [.r5, .r8, .r9] s t := ⟨fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [u.other _ hr.2.2, u₃.other _ hr.2.2, u₂.other _ hr.2.1, u₁.other _ hr.1],
      by rw [u.rd, u₃.rd, u₂.rd, u₁.rd], by rw [u.wr, u₃.wr, u₂.wr, u₁.wr]⟩
    refine ⟨⟨⟨h.of_keep K (by rw [u.mem, u₃.mem, u₂.mem, u₁.mem]) (by rw [sp, sp₃, sp₂, sp₁]), x⟩,
      kr.of_keep K⟩, ?_, ?_, ?_⟩
    · rw [u.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.gi.r28]
    · rw [u.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
    · rw [u.gpr, u₃.gpr]; rfl
  refine VP.pub (G := G) (fun σ s hs => ⟨hs.1.1.1.gi.r28, by rw [hs.1.1.1.gi.sp, ← hs.1.1.1.gi.hG]; rfl⟩)
    [.r29, .r30, .r31, .r5, .r8, .r9] cert (fun σ₁ σ₂ s₁ s₂ ⟨⟨_, a⟩, a5, a8, a9⟩ ⟨⟨_, b⟩, b5, b8, b9⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [a.r29, b.r29]
      · rw [a.r30, b.r30]
      · rw [a.r31, b.r31]
      · rw [a5, b5]
      · rw [a8, b8]
      · rw [a9, b9]) fun σ s ⟨⟨⟨h, x⟩, kr⟩, p5, p8, p9⟩ => ?_
  have gi := h.gi
  have big := gi.wBig
  have kb := gi.kBig
  have fit := gi.scrFit
  have hw := h.wsFull kr
  have l := h.lens
  have hjN := h.liveOk j hj
  have ok := hoc σ s ⟨h, x⟩
  simp only [ClOk, List.length_replicate] at ok
  have va := h.arrs.get hj
  have hsep : Region.Disjoint ⟨G.sa o, n⟩ G.rK := (gi.kdisj ok.2.1 ok.2.2).symm
  have hc : ∀ i < n, (⟨G.sa o, n⟩ : Region).Contains (G.sa o + BitVec.ofNat 64 i) 1 := fun i hi =>
    Offset.contains_base _ (by omega_using [hi]) (by omega_using [hn15, hi])
  refine WP.mono (storeBytes_ok hw hjN (by decide) p5 p8 p9 hn0 hnw
    (fun i hi => by
      show InRegions s.wr (G.sa o + BitVec.ofNat 64 i) 1
      rw [GP.sa_add]; exact gi.inScr (by omega_using [ok, hi]) (by omega_using []))
    (fun i hi x hx e => by subst e; exact absurd (past_of_disjoint' hsep (hc i hi)) (Nat.not_le.mpr hx))
    (by rw [GP.sa, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_using [ho15]),
      Nat.mod_eq_of_lt (by omega_using [hn0, fit, ok])]; omega_using [fit, ok])) fun t ⟨_, bt, ot, kt⟩ => ⟨⟨?_, x⟩, kr.of_keep ⟨kt.gpr, kt.rd, kt.wr⟩⟩
  have bs : Spec.Rsa.bytesAt t.mem (G.sa o) n = Spec.Rsa.i2osp (c.A j % 2 ^ (8 * n)) n := by
    rw [bytes_of_store hnw fun i hi => by rw [bt i hi]; rfl, Nat.pow_mul, va]
  refine h.of_scrs ⟨kt.gpr, kt.rd, kt.wr⟩ kt.sp (os := [(o, n)]) (fun p hp => ?_)
    ((frame_of_outside ot).mono (by simp)) fun y hy => ?_
  · simp only [List.mem_singleton] at hp; subst hp; simp only [ClOk, List.length_replicate]; omega_using [ok]
  rcases List.mem_cons.mp hy with rfl | hy
  · exact .inr ⟨by rw [VG.Proof.Rsa.i2osp_length]; exact bs, by simp only [ClOk, VG.Proof.Rsa.i2osp_length]; omega_using [ok]⟩
  · exact .inl ⟨(hcl y hy).1, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact (hcl y hy).2⟩

end

end VG.Proof.Dsa.PPC64LE.Gen

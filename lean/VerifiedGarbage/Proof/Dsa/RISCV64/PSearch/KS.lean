module

public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Bytes
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyOps
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyBytes
public import VerifiedGarbage.Proof.Rsa.RISCV64.KeyDiv
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.KernelRfl

-- separate module: the key working space's pieces, which both p's arithmetic (`PArith`) and the generator's step
-- (`GStep`) build on, apart from the key operations' many proofs it imports

/-! # DSA parameter search on RISC-V: steps in the key working space

As on PPC64LE (`Proof/Dsa/PPC64LE/Gen/KS.lean`, `KSOps.lean`, `KSSetup.lean`,
`KSLoad.lean`, `KSStore.lean`, `KSDiv.lean`), in words of 64 bits. The
operations on the arrays of the key working space
(`Impl/Rsa/RISCV64/KeyWs.lean`) are proven (`Proof/Rsa/RISCV64/KeyOps.lean`,
`KeyBytes.lean`, `KeyDiv.lean`) on any state whose writable regions hold the
working space, with its registers set (`Ws`): a state of the search does,
given the registers `KR` (`SS.ws`). `SS.ksOp` runs such code from a state of
the search, and `SS.of_ks` is the state after it: what the step wrote of the
arrays and slots, everything else as it was. Each operation is a piece
(`ks_vp`), its taint analysed with `s6` and the registers `KR` sets public.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Keys
open VG VG.RISCV64 VG.Proof.Mont

/-- Outside the arrays and header slots a step writes, memory is unchanged.
(As `Proof/Rsa/RISCV64/KeyLayout.lean` had it before #4344.) -/
theorem Frame.outside {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Frame B w js ds m m') {Z : Nat} (hj : ∀ j ∈ js, arr w j + S w ≤ Z) (hd : ∀ d ∈ ds, d + 8 ≤ Z) :
    Outside B 0 Z m m' :=
  fun x hx => h.out hj hd (by omega_arith)

/-- The frame of a step, the arrays below `N` and the slots in the header.
(As `Proof/Rsa/RISCV64/KeyLayout.lean` had it before #4344, which removed it
when nothing on `main` used it.) -/
theorem Ws.frame_out {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N) {js ds : List Nat}
    {m m' : Mem} (f : Frame B w js ds m m') (hj : ∀ j ∈ js, j < N) (hd : ∀ d ∈ ds, d + 8 ≤ hdr) :
    Outside B 0 Z m m' :=
  f.outside (fun j hj' => h.arr_fit (hj j hj')) fun d hd' => by have := hd d hd'; have := h.hdr_le; omega_arith

end VG.Proof.Rsa.RISCV64.Keys

namespace VG.Proof.Dsa.RISCV64.PSearch
open VG VG.RISCV64 VG.RISCV64.Steps VG.Proof.Mont
open VG.Proof.Rsa.RISCV64.Keys (Ws arr num slot S opRegs)
open VG.Impl.Dsa.RISCV64.ParameterSearch

/-- `A` with `j ↦ v`. -/
def KU (A : Nat → Nat) (j v : Nat) : Nat → Nat := fun i => if i = j then v else A i

@[simp] theorem KU_self (A : Nat → Nat) (j v : Nat) : KU A j v j = v := by simp [KU]
theorem KU_ne (A : Nat → Nat) {j i : Nat} (v : Nat) (h : i ≠ j) : KU A j v i = A i := by simp [KU, h]

/-- The memory frame of the key operations. -/
abbrev KKeep := VG.Proof.Rsa.RISCV64.Keys.Frame

/-- The key working space's registers: its words, its stride and its base. -/
structure KR (G : GP) (s : State) : Prop where
  s9 : s.gpr .s9 = BitVec.ofNat 64 G.w
  s10 : s.gpr .s10 = BitVec.ofNat 64 (S G.w)
  s11 : s.gpr .s11 = G.KB

theorem KR.of_keep {G : GP} {s t : State} {ws : List Reg} (h : KR G s) (k : Keep ws s t)
    (h9 : .s9 ∉ ws := by decide) (h10 : .s10 ∉ ws := by decide) (h11 : .s11 ∉ ws := by decide) : KR G t :=
  ⟨(k.gpr h9).trans h.s9, (k.gpr h10).trans h.s10, (k.gpr h11).trans h.s11⟩

/-- Bytes outside `[O, O + L)` kept, as a frame. -/
theorem frame_of_outside {O : Addr} {L : Nat} {m m' : Mem} (h : Outside O 0 L m m') :
    Frame [⟨O, L⟩] m m' := fun x hx => h x (.inr (by
  have := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at this
  show 0 + L ≤ (x - O).toNat
  omega))

section
variable {G : GP} {STK : Nat} {σ : State} {c : Cfg} {s : State}

theorem SS.kbNat (h : SS G STK σ c s) : G.KB.toNat = G.scr.toNat + kB G.pLen := by
  have := h.gi.wBig; have := h.gi.kBig; have := h.gi.scrFit
  have : 0 < G.pLen := by rcases h.lens with e | e | e <;> omega
  rw [GP.KB, GP.sa, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show kB G.pLen < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (by omega)]

/-- The key working space, within `scratch`. -/
theorem SS.ws (h : SS G STK σ c s) (hr : KR G s) : Ws s G.KB (kz G.pLen) G.w nArrs := by
  have := h.gi.wBig; have := h.gi.kBig; have := h.gi.scrFit; have al := h.gi.scrAl
  have e := h.kbNat
  have l := h.lens
  have k4 := (lay_ok l).2.2.2.2.1
  have inS : G.rScr ∈ s.wr := by rw [h.gi.wr, h.gi.pre.wr, h.gi.hG]; simp
  refine ⟨⟨⟨G.scr, kB G.pLen, G.scrLen * 8, inS, rfl, by omega, by omega⟩, by omega, by omega⟩,
    ?_, ?_, ?_, hr.s9, hr.s10, hr.s11⟩ <;>
    simp only [arr, S, Impl.Rsa.RISCV64.Keys.hdr, nArrs, kz, GP.w] <;> rcases l with e | e | e <;> rw [e] <;> decide

/-- A step in the key working space, from a state of the search: what it
keeps, with the stack pointer and the frame of the working space. -/
theorem SS.ksOp (h : SS G STK σ c s) (hr : KR G s) {code : Prog isa} {js ds : List Nat}
    (hj : ∀ j ∈ js, j < nArrs) (hd : ∀ d ∈ ds, d + 8 ≤ Impl.Rsa.RISCV64.Keys.hdr)
    {P : State → Prop} {ws : List Reg}
    (hwp : WP isa code s fun t => Ws t G.KB (kz G.pLen) G.w nArrs ∧ KKeep G.KB G.w js ds s.mem t.mem ∧ P t ∧
      Keep ws s t) {Q : State → Prop}
    (k : ∀ t, KKeep G.KB G.w js ds s.mem t.mem → P t → Keep ws s t → t.sp = s.sp →
      Frame [G.rK] s.mem t.mem → Q t) :
    WP isa code s Q :=
  WP.sp_eq (WP.mono hwp fun t ⟨_, kp, p, r⟩ sp =>
    k t kp p r sp (frame_of_outside ((h.ws hr).frame_out kp hj hd)))

/-- After a step in the key working space: its arrays and slots. -/
theorem SS.of_ks (h : SS G STK σ c s) {t : State} {ws : List Reg} (r : Keep ws s t) (sp : t.sp = s.sp)
    (f : Frame [G.rK] s.mem t.mem) {A : Nat → Nat} {live : List Nat} {KV : Nat → Nat} {kls : List Nat}
    (ha : ∀ j ∈ live, num t.mem G.KB G.w j = A j) (hl : ∀ j ∈ live, j < nArrs)
    (hk : ∀ d ∈ kls, slot t.mem G.KB d = KV d) (hko : ∀ d ∈ kls, KlsOk d) (h6 : .s6 ∉ ws := by decide) :
    SS G STK σ { c with A := A, live := live, KV := KV, kls := kls } t := by
  have gi := h.gi
  have big := gi.wBig
  have kb := gi.kBig
  have hE : hEnd ≤ kB G.pLen := by rcases gi.lens with e | e | e <;> rw [e] <;> decide
  refine ⟨gi.of_scr r sp (o := kB G.pLen) (n := kz G.pLen) hE (by omega) (f.mono (by simp)) h6,
    h.sb.frame f (fun x hx r hr => ?_) (fun x hx => ?_), h.clOk, ha, hl, hk, hko⟩
  · rw [List.mem_singleton] at hr; subst hr
    have := h.clOk x hx
    exact (gi.kdisj this.2.1 this.2.2).symm
  · have := (h.clOk x hx).2.2; have := gi.scrFit; omega

/-- After an operation that writes the array `o` (to `v`) and no slot. -/
theorem SS.of_op (h : SS G STK σ c s) {t : State} {ws : List Reg} (r : Keep ws s t) (sp : t.sp = s.sp)
    (f : Frame [G.rK] s.mem t.mem) {o v : Nat} (ho : o < nArrs) (kp : KKeep G.KB G.w [o] [] s.mem t.mem)
    (e : num t.mem G.KB G.w o = v) (h6 : .s6 ∉ ws := by decide) :
    SS G STK σ { c with A := KU c.A o v, live := o :: c.live } t := by
  have l := h.lens
  refine h.of_ks r sp f (fun j hj => ?_) (fun j hj => ?_) (fun d hd => ?_) h.kslOk h6
  · by_cases hjo : j = o
    · subst hjo; rw [KU_self]; exact e
    · have hjl := (List.mem_cons.mp hj).resolve_left hjo
      rw [KU_ne _ _ hjo, kp.num (by simpa using fun e => hjo e.symm) (by simp)
        (by have := arrs_fit (L := G.pLen) (h.liveOk j hjl); have := kz_le l; simp only [GP.w]; omega)]
      exact h.arrs j hjl
  · rcases List.mem_cons.mp hj with rfl | hj
    · exact ho
    · exact h.liveOk j hj
  · rw [kp.slot (h.kslOk d hd).1 (by simp)]; exact h.ksl d hd

/-- After an operation that writes the slot `d` (to `v`) and no array. -/
theorem SS.of_opS (h : SS G STK σ c s) {t : State} {ws : List Reg} (r : Keep ws s t) (sp : t.sp = s.sp)
    (f : Frame [G.rK] s.mem t.mem) {d v : Nat} (hd : KlsOk d) (kp : KKeep G.KB G.w [] [d] s.mem t.mem)
    (e : slot t.mem G.KB d = v) (h6 : .s6 ∉ ws := by decide) :
    SS G STK σ { c with KV := KU c.KV d v, kls := d :: c.kls } t := by
  have l := h.lens
  refine h.of_ks r sp f (fun j hj => ?_) h.liveOk (fun e' he => ?_) (fun e' he => ?_) h6
  · rw [kp.num (by simp) (by simpa using hd.1)
      (by have := arrs_fit (L := G.pLen) (h.liveOk j hj); have := kz_le l; simp only [GP.w]; omega)]
    exact h.arrs j hj
  · by_cases hed : e' = d
    · subst hed; rw [KU_self]; exact e
    · rcases List.mem_cons.mp he with rfl | he
      · exact absurd rfl hed
      rw [KU_ne _ _ hed, kp.slot (h.kslOk e' he).1 (by
        simp only [List.mem_singleton, forall_eq]
        have := h.kslOk e' he; have := hd; simp only [KlsOk] at *; omega)]
      exact h.ksl e' he
  · rcases List.mem_cons.mp he with rfl | he
    · exact hd
    · exact h.kslOk e' he

end

/-! ## The operations as pieces -/

/-- A stage of the arithmetic. -/
abbrev KSt (G : GP) (c : Cfg) (X : State → Prop) (σ s : State) : Prop := St G c X σ s ∧ KR G s

/-- The taint analysis of code in the key working space. -/
abbrev CertK (code : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s6, .s9, .s10, .s11]) code hc).isSome = true

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- A piece in the key working space. -/
theorem ks_vp {F Q : State → State → Prop} {cf : State → Cfg} {code : Prog isa} (cert : CertK code)
    (hF : ∀ σ s, F σ s → SS G STK0 σ (cf σ) s ∧ KR G s) (wp : ∀ σ s, F σ s → WP isa code s (Q σ)) :
    VP F code Q :=
  VP.pub (G := G) (fun σ s hs => ⟨(hF σ s hs).1.gi.s6, by rw [(hF σ s hs).1.gi.sp, ← (hF σ s hs).1.gi.hG]; rfl⟩)
    [.s9, .s10, .s11] cert (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
      have a := (hF _ _ h₁).2; have b := (hF _ _ h₂).2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a.s9, b.s9]
      · rw [a.s10, b.s10]
      · rw [a.s11, b.s11]) wp

theorem num_lt (m : Mem) (B : Addr) (w j : Nat) : num m B w j < 2 ^ (64 * w) := wordsVal_lt _ _ _ _

/-- `[o] := [a] − [b]`, for `[b] ≤ [a]`. -/
theorem sub3_vp {o a b : Nat} (cert : CertK (Impl.Rsa.RISCV64.Keys.sub3 o a b)) (ho : o < nArrs)
    (ha : a ∈ c.live) (hb : b ∈ c.live) (hoa : o ≠ a) (hob : o ≠ b) (hle : c.A b ≤ c.A a) :
    VP (KSt G c X) (Impl.Rsa.RISCV64.Keys.sub3 o a b)
      (KSt G { c with A := KU c.A o (c.A a - c.A b), live := o :: c.live } X) := by
  refine ks_vp cert (fun σ s h => ⟨h.1.1, h.2⟩) fun σ s ⟨⟨h, x⟩, kr⟩ => ?_
  have hw := h.ws kr
  have va := h.arrs a ha
  have vb := h.arrs b hb
  refine h.ksOp kr (js := [o]) (ds := []) (by simpa using ho) (by simp)
    (P := fun t => num t.mem G.KB G.w o + num s.mem G.KB G.w b =
      num s.mem G.KB G.w a + 2 ^ (64 * G.w) * (t.gpr .t4).toNat ∧ (t.gpr .t4).toNat ≤ 1)
    ((VG.Proof.Rsa.RISCV64.Keys.sub3_ok hw ho (h.liveOk a ha) (h.liveOk b hb) (by decide) hoa hob).mono
      fun t ⟨w, k, v, br, r⟩ => ⟨w, k, ⟨v, br⟩, r⟩)
    fun t k ⟨v, br⟩ R sp f => ⟨⟨h.of_op R sp f ho k ?_, x⟩, kr.of_keep R⟩
  rw [va, vb] at v
  have lt := num_lt t.mem G.KB G.w o
  have alt : c.A a < 2 ^ (64 * G.w) := va ▸ num_lt _ _ _ _
  generalize 2 ^ (64 * G.w) = M at v lt alt
  rcases (by omega : (t.gpr .t4).toNat = 0 ∨ (t.gpr .t4).toNat = 1) with e | e <;> rw [e] at v
  · omega
  · have : M * 1 = M := Nat.mul_one M
    omega

/-- `[o] := [b]` if the slot `sl` is 1, else `[a]`. -/
theorem sel_vp {o a b sl : Nat} (cert : CertK (Impl.Rsa.RISCV64.Keys.sel o a b sl)) (ho : o < nArrs)
    (ha : a ∈ c.live) (hb : b ∈ c.live) (hoa : o ≠ a) (hob : o ≠ b) (hsl : sl ∈ c.kls) (bit : c.KV sl ≤ 1) :
    VP (KSt G c X) (Impl.Rsa.RISCV64.Keys.sel o a b sl)
      (KSt G { c with A := KU c.A o (if c.KV sl = 0 then c.A a else c.A b), live := o :: c.live } X) := by
  refine ks_vp cert (fun σ s h => ⟨h.1.1, h.2⟩) fun σ s ⟨⟨h, x⟩, kr⟩ => ?_
  have hw := h.ws kr
  have va := h.arrs a ha
  have vb := h.arrs b hb
  have vs := h.ksl sl hsl
  refine h.ksOp kr (js := [o]) (ds := []) (by simpa using ho) (by simp) (P := fun t => num t.mem G.KB G.w o =
      (if slot s.mem G.KB sl = 0 then num s.mem G.KB G.w a else num s.mem G.KB G.w b))
    ((VG.Proof.Rsa.RISCV64.Keys.sel_ok hw ho (h.liveOk a ha) (h.liveOk b hb) (by decide) hoa hob
      (h.kslOk sl hsl).1 (h.kslOk sl hsl).2 (by rw [vs]; exact bit)).mono fun t ⟨w, k, v, r⟩ => ⟨w, k, v, r⟩)
    fun t k v R sp f => ⟨⟨h.of_op R sp f ho k (by rw [v, va, vb, vs]), x⟩, kr.of_keep R⟩

/-- `[o] := [a]`. -/
theorem copy_vp {o a : Nat} (cert : CertK (Impl.Rsa.RISCV64.Keys.copy o a)) (ho : o < nArrs) (ha : a ∈ c.live)
    (hoa : o ≠ a) :
    VP (KSt G c X) (Impl.Rsa.RISCV64.Keys.copy o a) (KSt G { c with A := KU c.A o (c.A a), live := o :: c.live } X) := by
  refine ks_vp cert (fun σ s h => ⟨h.1.1, h.2⟩) fun σ s ⟨⟨h, x⟩, kr⟩ => ?_
  have hw := h.ws kr
  have va := h.arrs a ha
  refine h.ksOp kr (js := [o]) (ds := []) (by simpa using ho) (by simp)
    (P := fun t => num t.mem G.KB G.w o = num s.mem G.KB G.w a)
    ((VG.Proof.Rsa.RISCV64.Keys.copy_ok hw ho (h.liveOk a ha) (by decide) hoa).mono
      fun t ⟨w, k, v, r, _⟩ => ⟨w, k, v, r⟩)
    fun t k v R sp f => ⟨⟨h.of_op R sp f ho k (by rw [v, va]), x⟩, kr.of_keep R⟩

/-- The slot `sl` := `[j]`'s low bit. -/
theorem bitOf_vp {sl j : Nat} (cert : CertK (.block (Impl.Rsa.RISCV64.Keys.bitOf sl j))) (hj : j ∈ c.live)
    (hsl : KlsOk sl) :
    VP (KSt G c X) (.block (Impl.Rsa.RISCV64.Keys.bitOf sl j))
      (KSt G { c with KV := KU c.KV sl (c.A j % 2), kls := sl :: c.kls } X) := by
  refine ks_vp cert (fun σ s h => ⟨h.1.1, h.2⟩) fun σ s ⟨⟨h, x⟩, kr⟩ => ?_
  have hw := h.ws kr
  have va := h.arrs j hj
  refine h.ksOp kr (js := []) (ds := [sl]) (by simp) (by simpa using hsl.1)
    (P := fun t => slot t.mem G.KB sl = num s.mem G.KB G.w j % 2)
    ((VG.Proof.Rsa.RISCV64.Keys.bitOf_ok hw (h.liveOk j hj) (by decide) hsl.1 hsl.2).mono
      fun t ⟨w, k, v, r⟩ => ⟨w, k, v, r⟩)
    fun t k v R sp f => ⟨⟨h.of_opS R sp f hsl k (by rw [v, va]), x⟩, kr.of_keep R⟩

/-- `[j]`'s low bit set. -/
theorem orOne_vp {j : Nat} (cert : CertK (.block (Impl.Rsa.RISCV64.Keys.orOne j))) (hj : j ∈ c.live) :
    VP (KSt G c X) (.block (Impl.Rsa.RISCV64.Keys.orOne j))
      (KSt G { c with A := KU c.A j (c.A j / 2 * 2 + 1), live := j :: c.live } X) := by
  refine ks_vp cert (fun σ s h => ⟨h.1.1, h.2⟩) fun σ s ⟨⟨h, x⟩, kr⟩ => ?_
  have hw := h.ws kr
  have va := h.arrs j hj
  refine h.ksOp kr (js := [j]) (ds := []) (by simpa using h.liveOk j hj) (by simp)
    (P := fun t => num t.mem G.KB G.w j = num s.mem G.KB G.w j / 2 * 2 + 1)
    ((VG.Proof.Rsa.RISCV64.Keys.orOne_ok hw (h.liveOk j hj) (by decide)).mono fun t ⟨w, k, v, r⟩ => ⟨w, k, v, r⟩)
    fun t k v R sp f => ⟨⟨h.of_op R sp f (h.liveOk j hj) k (by rw [v, va]), x⟩, kr.of_keep R⟩

/-- `[j]`'s low bit cleared. -/
theorem clrLow_vp {j : Nat} (cert : CertK (.block (Impl.Rsa.RISCV64.Keys.clrLow j))) (hj : j ∈ c.live) :
    VP (KSt G c X) (.block (Impl.Rsa.RISCV64.Keys.clrLow j))
      (KSt G { c with A := KU c.A j (c.A j / 2 * 2), live := j :: c.live } X) := by
  refine ks_vp cert (fun σ s h => ⟨h.1.1, h.2⟩) fun σ s ⟨⟨h, x⟩, kr⟩ => ?_
  have hw := h.ws kr
  have va := h.arrs j hj
  refine h.ksOp kr (js := [j]) (ds := []) (by simpa using h.liveOk j hj) (by simp)
    (P := fun t => num t.mem G.KB G.w j = num s.mem G.KB G.w j / 2 * 2)
    ((VG.Proof.Rsa.RISCV64.Keys.clrLow_ok hw (h.liveOk j hj) (by decide)).mono fun t ⟨w, k, v, r⟩ => ⟨w, k, v, r⟩)
    fun t k v R sp f => ⟨⟨h.of_op R sp f (h.liveOk j hj) k (by rw [v, va]), x⟩, kr.of_keep R⟩

end

end VG.Proof.Dsa.RISCV64.PSearch

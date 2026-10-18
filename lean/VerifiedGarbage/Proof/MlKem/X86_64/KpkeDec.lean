module

public import VerifiedGarbage.Proof.MlKem.X86_64.InlinePrim
public import VerifiedGarbage.Proof.MlKem.X86_64.TopBase
public import VerifiedGarbage.Impl.MlKem.X86_64.Kpke16
public import VerifiedGarbage.Spec.MlKem.Kpke16
public import VerifiedGarbage.Proof.MlKem.KPke
public import VerifiedGarbage.Proof.MlKem.X86_64.EncBase
import VerifiedGarbage.Proof.MlKem.X86_64.DcDec
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
import VerifiedGarbage.Proof.Sha3.X86_64.X4.Wp

/-!
# ML-KEM on x86-64: `vg_mlkem*_kpke_decrypt`

The contract (`kpkeDecK`), what holds throughout the function (`KT`: its
pointers, the saved registers, its inputs), and the steps: the prologue,
each polynomial primitive inline (`KT.step` keeps `KT` across one that
writes only below the saved registers), and the epilogue.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- The size of the K-PKE functions' `scratch`. -/
abbrev kScr : Nat := 16384

/-- `vg_mlkem*_kpke_decrypt(m = rdi, s = rsi, ct = rdx, scratch = rcx)` of the parameter set `L`. -/
def kpkeDecK (L : Kem) : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rsi, 384 * L.k⟩, ⟨s.gpr .rdx, L.ctLen⟩] ∧ s.wr = [⟨s.gpr .rdi, 32⟩, ⟨s.gpr .rcx, kScr⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, 32⟩ ⟨s.gpr .rsi, 384 * L.k⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, 32⟩ ⟨s.gpr .rdx, L.ctLen⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, 32⟩ ⟨s.gpr .rcx, kScr⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, 384 * L.k⟩ ⟨s.gpr .rcx, kScr⟩ ∧
    Region.Disjoint ⟨s.gpr .rdx, L.ctLen⟩ ⟨s.gpr .rcx, kScr⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, 32⟩ ∧ (retR s).Disjoint ⟨s.gpr .rsi, 384 * L.k⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdx, L.ctLen⟩ ∧ (retR s).Disjoint ⟨s.gpr .rcx, kScr⟩ ∧
    (s.gpr .rdi).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 384 * L.k ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + L.ctLen ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + kScr ≤ 2 ^ 64
  post s s' := bytesAt s'.mem (s.gpr .rdi) 32 =
    kpkeDecrypt L.p (bytesAt s.mem (s.gpr .rsi) (384 * L.k)) (bytesAt s.mem (s.gpr .rdx) L.ctLen)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

namespace KpkeDec

open VG.Impl.MlKem.X86_64.Kpke16

/-- The polynomials and the working space lie below this offset of `scratch`. -/
abbrev oTop : Nat := 14336

/-- What holds throughout the function entered in `σ`. -/
structure KT (L : Kem) (σ s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  rsp : s.gpr .rsp = σ.gpr .rsp
  rbx : s.gpr .rbx = σ.gpr .rcx
  rbp : s.gpr .rbp = σ.gpr .rsi
  r12 : s.gpr .r12 = σ.gpr .rdi
  r13 : s.gpr .r13 = σ.gpr .rdx
  r14 : s.gpr .r14 = σ.gpr .r14
  r15 : s.gpr .r15 = σ.gpr .r15
  saved : ∀ i < 4, s.mem.readW (σ.gpr .rcx + BitVec.ofNat 64 (oKS + 8 * i)) 64 = σ.gpr (kRegs.getD i .rbx)
  ret : s.mem.readW (σ.gpr .rsp) 64 = σ.mem.readW (σ.gpr .rsp) 64
  bS : bytesAt s.mem (σ.gpr .rsi) (384 * L.k) = bytesAt σ.mem (σ.gpr .rsi) (384 * L.k)
  bT : bytesAt s.mem (σ.gpr .rdx) L.ctLen = bytesAt σ.mem (σ.gpr .rdx) L.ctLen

section
variable {L : Kem} {σ : State} (hp : (kpkeDecK L).pre σ)
include hp

omit hp in
/-- The working space below `oTop` lies in `scratch`. -/
theorem sub_top : Region.Sub ⟨σ.gpr .rcx, oTop⟩ ⟨σ.gpr .rcx, kScr⟩ := Region.sub_prefix (by decide)

/-- A region of the working space below `oTop` is apart from the inputs, the output, the
saved registers and the return address. -/
theorem top_disj {r : Region} (hr : Region.Sub r ⟨σ.gpr .rcx, oTop⟩) :
    Region.Disjoint ⟨σ.gpr .rsi, 384 * L.k⟩ r ∧ Region.Disjoint ⟨σ.gpr .rdx, L.ctLen⟩ r ∧
      Region.Disjoint ⟨σ.gpr .rdi, 32⟩ r ∧ (retR σ).Disjoint r ∧
      ∀ i < 4, Region.Disjoint ⟨σ.gpr .rcx + BitVec.ofNat 64 (oKS + 8 * i), 8⟩ r := by
  obtain ⟨_, _, _, _, d3, d4, d5, _, _, _, r4, _, _, _, _⟩ := id hp
  have hs := fun (R : Region) (h : R.Disjoint ⟨σ.gpr .rcx, kScr⟩) => (h.sub_right sub_top).sub_right hr
  refine ⟨hs _ d4, hs _ d5, hs _ d3, hs _ r4, fun i hi => ?_⟩
  exact (Offset.disjoint_base (σ.gpr .rcx) (d := oKS + 8 * i) (n := 8) (k := oTop)
    (by simp only [oKS, oTop]; omega) (by simp only [oKS]; omega)).sub_right hr

theorem KT.step {s s' : State} (h : KT L σ s) {W : List Region} (hP : IPost s s' W)
    (hW : ∀ r ∈ W, Region.Sub r ⟨σ.gpr .rcx, oTop⟩) : KT L σ s' := by
  have D := fun r hr => top_disj hp (r := r) (hW r hr)
  have nS := hp.2.2.2.2.2.2.2.2.2.2.2.2.1
  have nT := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨hP.rd.trans h.rd, hP.wr.trans h.wr, hP.rsp.trans h.rsp, (hP.cs .rbx (by decide)).trans h.rbx,
    (hP.cs .rbp (by decide)).trans h.rbp, (hP.cs .r12 (by decide)).trans h.r12, (hP.cs .r13 (by decide)).trans h.r13,
    (hP.cs .r14 (by decide)).trans h.r14, (hP.cs .r15 (by decide)).trans h.r15, fun i hi => ?_, ?_, ?_, ?_⟩
  · rw [hP.frame.readW (Region.contains_self _ _) (fun r hr => (D r hr).2.2.2.2 i hi) (by decide)]
    exact h.saved i hi
  · rw [hP.frame.readW (Region.contains_self _ _) (fun r hr => (D r hr).2.2.2.1) (by decide)]
    exact h.ret
  · rw [bytesAt_frame hP.frame (fun r hr => (D r hr).1) (by omega)]; exact h.bS
  · rw [bytesAt_frame hP.frame (fun r hr => (D r hr).2.1) (by omega)]; exact h.bT

/-! ## The prologue -/

omit hp in
theorem pro_eq : pro = [.store (at_ .rcx 14336) .rbx, .store (at_ .rcx 14344) .rbp, .store (at_ .rcx 14352) .r12,
    .store (at_ .rcx 14360) .r13, .mov .rbx (.reg .rcx), .mov .rbp (.reg .rsi), .mov .r12 (.reg .rdi),
    .mov .r13 (.reg .rdx)] := rfl

omit hp in
/-- The four stores of `pro`: each slot holds its register. -/
theorem stores_read (m : Mem) (a : Addr) (v : Nat → BitVec 64) : ∀ i < 4,
    ((((m.writeW (a + BitVec.ofNat 64 14336) (v 0)).writeW (a + BitVec.ofNat 64 14344) (v 1)).writeW
      (a + BitVec.ofNat 64 14352) (v 2)).writeW (a + BitVec.ofNat 64 14360) (v 3)).readW
      (a + BitVec.ofNat 64 (oKS + 8 * i)) 64 = v i := by
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  all_goals
    simp (disch := omega) only [oKS, Nat.reduceMul, Nat.reduceAdd, readW_writeW_slot, Mem.readW_writeW_self64]

theorem pro_ok : WP isa (.block pro) σ (KT L σ) := by
  obtain ⟨hrd, hwr, _, _, _, d4, d5, _, _, _, r4, _, nS, nT, nC⟩ := id hp
  have hS : ⟨σ.gpr .rcx, kScr⟩ ∈ σ.wr := by rw [hwr]; simp
  have c : ∀ o, o + 8 ≤ kScr → (⟨σ.gpr .rcx, kScr⟩ : Region).Contains (σ.gpr .rcx + BitVec.ofNat 64 o) 8 :=
    fun o ho => Offset.contains_base _ ho (by omega)
  have w : ∀ o, o + 8 ≤ kScr → InRegions σ.wr (σ.gpr .rcx + BitVec.ofNat 64 o) 8 := fun o ho => ⟨_, hS, c o ho⟩
  have w0 := w 14336 (by decide); have w1 := w 14344 (by decide); have w2 := w 14352 (by decide)
  have w3 := w 14360 (by decide)
  rw [pro_eq]
  refine WP.mono (WP.keep [.rbx, .rbp, .r12, .r13] (Q := fun s =>
    s.mem = (((σ.mem.writeW (σ.gpr .rcx + BitVec.ofNat 64 14336) (σ.gpr .rbx)).writeW
      (σ.gpr .rcx + BitVec.ofNat 64 14344) (σ.gpr .rbp)).writeW (σ.gpr .rcx + BitVec.ofNat 64 14352) (σ.gpr .r12)).writeW
      (σ.gpr .rcx + BitVec.ofNat 64 14360) (σ.gpr .r13) ∧
    s.gpr .rbx = σ.gpr .rcx ∧ s.gpr .rbp = σ.gpr .rsi ∧ s.gpr .r12 = σ.gpr .rdi ∧ s.gpr .r13 = σ.gpr .rdx)
    (by xrun [w0, w1, w2, w3]) (by decide)) fun s ⟨⟨hm, hbx, hbp, h12, h13⟩, k⟩ => ?_
  have hf : Frame [⟨σ.gpr .rcx, kScr⟩] σ.mem s.mem := by
    rw [hm]
    exact (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 14336 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 14344 (by decide))).writeW (List.mem_singleton_self _) _
      (c 14352 (by decide))).writeW (List.mem_singleton_self _) _ (c 14360 (by decide)))
  refine ⟨k.2.1, k.2.2, k.gpr (by decide), hbx, hbp, h12, h13, k.gpr (by decide), k.gpr (by decide),
    fun i hi => ?_, ?_, ?_, ?_⟩
  · rw [hm]
    exact stores_read σ.mem (σ.gpr .rcx) (fun i => σ.gpr (kRegs.getD i .rbx)) i hi
  · exact hf.readW (Region.contains_self _ _) (by simpa using r4) (by decide)
  · exact bytesAt_frame hf (by simpa using d4) (by omega)
  · exact bytesAt_frame hf (by simpa using d5) (by omega)

/-! ## The epilogue -/

omit hp in
theorem epi_eq : epi = [.mov .r13 (.mem (at_ .rbx 14360)), .mov .r12 (.mem (at_ .rbx 14352)),
    .mov .rbp (.mem (at_ .rbx 14344)), .mov .rbx (.mem (at_ .rbx 14336))] := rfl

theorem epi_ok {s : State} (h : KT L σ s) :
    WP isa (.block epi) s fun s' => gprPreserved σ s' ∧ s'.mem = s.mem := by
  obtain ⟨_, hwr, _, _, _, _, _, _, _, _, _, _, _, _, nC⟩ := id hp
  have hS : ⟨σ.gpr .rcx, kScr⟩ ∈ s.wr := by rw [h.wr, hwr]; simp
  have i : ∀ j < 4, InRegions (s.rd ++ s.wr) (s.gpr .rbx + BitVec.ofNat 64 (oKS + 8 * j)) 8 := fun j hj =>
    ⟨_, List.mem_append_right _ hS, by
      rw [h.rbx]; exact Offset.contains_base _ (by simp only [oKS, kScr]; omega) (by simp only [oKS]; omega)⟩
  have e : ∀ j < 4, s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 (oKS + 8 * j)) 64 = σ.gpr (kRegs.getD j .rbx) :=
    fun j hj => by rw [h.rbx]; exact h.saved j hj
  have e0 := e 0 (by decide); have e1 := e 1 (by decide); have e2 := e 2 (by decide); have e3 := e 3 (by decide)
  have i0 := i 0 (by decide); have i1 := i 1 (by decide); have i2 := i 2 (by decide); have i3 := i 3 (by decide)
  simp only [oKS, kRegs, List.getD_cons_zero, List.getD_cons_succ, Nat.reduceMul, Nat.reduceAdd] at e0 e1 e2 e3 i0 i1 i2 i3
  rw [epi_eq]
  refine WP.mono (WP.keep [.r13, .r12, .rbp, .rbx] (Q := fun s' =>
    s'.gpr .r13 = σ.gpr .r13 ∧ s'.gpr .r12 = σ.gpr .r12 ∧ s'.gpr .rbp = σ.gpr .rbp ∧ s'.gpr .rbx = σ.gpr .rbx ∧
    s'.mem = s.mem) (by xrun [i0, i1, i2, i3, e0, e1, e2, e3]) (by decide))
    fun s' ⟨⟨h13, h12, hbp, hbx, hm⟩, k⟩ => ⟨⟨fun r hr => ?_, ?_⟩, hm⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hbx, hbp, by rw [k.gpr (by decide), h.rsp], h12, h13, by rw [k.gpr (by decide), h.r14],
      by rw [k.gpr (by decide), h.r15]]
  · rw [hm]; exact h.ret

/-! ## Regions -/

section
variable {s : State} (h : KT L σ s)
include h

theorem inT {o n : Nat} (ho : o + n ≤ L.ctLen) (hn : 0 < n) : InRegions (s.rd ++ s.wr) (σ.gpr .rdx + BitVec.ofNat 64 o) n := by
  obtain ⟨hrd, _, _, _, _, _, _, _, _, _, _, _, _, nT, _⟩ := id hp
  exact ⟨_, List.mem_append_left _ (by rw [h.rd, hrd]; simp), Offset.contains_base _ ho (by omega)⟩

theorem inS {o n : Nat} (ho : o + n ≤ 384 * L.k) (hn : 0 < n) :
    InRegions (s.rd ++ s.wr) (σ.gpr .rsi + BitVec.ofNat 64 o) n := by
  obtain ⟨hrd, _, _, _, _, _, _, _, _, _, _, _, nS, _, _⟩ := id hp
  exact ⟨_, List.mem_append_left _ (by rw [h.rd, hrd]; simp), Offset.contains_base _ ho (by omega)⟩

theorem inC {o n : Nat} (ho : o + n ≤ kScr) : InRegions s.wr (σ.gpr .rcx + BitVec.ofNat 64 o) n := by
  obtain ⟨_, hwr, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := id hp
  exact ⟨_, by rw [h.wr, hwr]; simp, Offset.contains_base _ ho (by simp only [kScr] at ho; omega)⟩

theorem inM : InRegions s.wr (σ.gpr .rdi + BitVec.ofNat 64 0) 32 := by
  obtain ⟨_, hwr, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := id hp
  exact ⟨_, by rw [h.wr, hwr]; simp, Offset.contains_base _ (Nat.le_refl _) (by omega)⟩

omit hp in
theorem retR_eq : retR s = retR σ := by simp only [retR, h.rsp]

end

omit hp in
/-- A polynomial of the working space below `oTop`. -/
theorem qSub {i : Nat} (hi : i < 10) :
    Region.Sub (pR (σ.gpr .rcx + BitVec.ofNat 64 (oQ i))) ⟨σ.gpr .rcx, oTop⟩ :=
  Offset.sub_base _ (by simp only [oQ, oTop]; omega)

omit hp in
theorem qScr {i : Nat} (hi : i < 10) :
    Region.Sub (pR (σ.gpr .rcx + BitVec.ofNat 64 (oQ i))) ⟨σ.gpr .rcx, kScr⟩ :=
  fun x hx => sub_top x (qSub hi x hx)

omit hp in
theorem qDisj {i j : Nat} (hi : i < 10) (hj : j < 10) (hij : i ≠ j) :
    (pR (σ.gpr .rcx + BitVec.ofNat 64 (oQ i))).Disjoint (pR (σ.gpr .rcx + BitVec.ofNat 64 (oQ j))) :=
  Offset.disjoint _ (by simp only [oQ]; omega) (by simp only [oQ]; omega) (by simp only [oQ]; omega)

/-! ## `u'` and `ŝ` -/

/-- The ciphertext and the decryption key. -/
abbrev cB (L : Kem) (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdx) L.ctLen
abbrev dB (L : Kem) (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rsi) (384 * L.k)

/-- The first `nu` of `u'` and `ns` of `ŝ` are done. -/
structure DR (L : Kem) (σ : State) (nu ns : Nat) (s : State) : Prop where
  kt : KT L σ s
  u : ∀ i < nu, PolyIs s.mem (σ.gpr .rcx + BitVec.ofNat 64 (oQ i)) (KPke.dcU L.p (cB L σ) i)
  sh : ∀ i < ns, PolyIs s.mem (σ.gpr .rcx + BitVec.ofNat 64 (oQ (L.k + i))) (dcS (dB L σ) i)

theorem DR.keep {nu ns : Nat} {s s' : State} (h : DR L σ nu ns s) {i : Nat} (hi : i < 10) (hk : L.k ≤ 4)
    (hP : IPost s s' [pR (σ.gpr .rcx + BitVec.ofNat 64 (oQ i))]) (hu : nu ≤ i ∨ i ≤ L.k + ns ∧ L.k ≤ i ∧ nu ≤ L.k)
    (hs : ns ≤ 4) :
    KT L σ s' ∧ (∀ j < nu, PolyIs s'.mem (σ.gpr .rcx + BitVec.ofNat 64 (oQ j)) (KPke.dcU L.p (cB L σ) j)) ∧
      ∀ j < ns, j + L.k ≠ i →
        PolyIs s'.mem (σ.gpr .rcx + BitVec.ofNat 64 (oQ (L.k + j))) (dcS (dB L σ) j) := by
  have hW : ∀ r ∈ [pR (σ.gpr .rcx + BitVec.ofNat 64 (oQ i))], Region.Sub r ⟨σ.gpr .rcx, oTop⟩ := by
    intro r hr; rw [List.mem_singleton] at hr; subst hr; exact qSub hi
  refine ⟨h.kt.step hp hP hW, fun j hj => polyIs_frame hP.frame ?_ (h.u j hj), fun j hj hji =>
    polyIs_frame hP.frame ?_ (h.sh j hj)⟩
  · intro r hr; rw [List.mem_singleton] at hr; subst hr
    exact qDisj (by omega) hi (by omega)
  · intro r hr; rw [List.mem_singleton] at hr; subst hr
    exact qDisj (by omega) hi (by omega)

/-- What the proofs need of the parameter set, decided for each. -/
structure KdWf (L : Kem) : Prop where
  k34 : L.k = 3 ∨ L.k = 4
  du : 0 < L.du ∧ L.du ≤ 11
  dv : 0 < L.dv ∧ L.dv ≤ 11
  ct : L.ctLen < 2 ^ 16

omit hp in
theorem na_rbx (o : Nat) : NA ((.rbx, o) : Ptr) := by simp [NA, argRegs]

omit hp in
theorem pa_q (s : State) (h : KT L σ s) (i : Nat) :
    pa s (qP i) = σ.gpr .rcx + BitVec.ofNat 64 (oQ i) := by
  simp only [pa, h.rbx]

omit hp in
theorem pa_r13 (s : State) (h : KT L σ s) (o : Nat) :
    pa s (.r13, o) = σ.gpr .rdx + BitVec.ofNat 64 o := by
  simp only [pa, h.r13]

omit hp in
theorem pa_rbp (s : State) (h : KT L σ s) (o : Nat) :
    pa s (.rbp, o) = σ.gpr .rsi + BitVec.ofNat 64 o := by
  simp only [pa, h.rbp]

theorem inC' {s : State} (h : KT L σ s) {o n : Nat} (ho : o + n ≤ kScr) :
    InRegions (s.rd ++ s.wr) (σ.gpr .rcx + BitVec.ofNat 64 o) n := by
  obtain ⟨r, hr, hc⟩ := inC hp h ho
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem u_ok {A : Arith} {wc wd : List Nat} (K : KemCalls L wc wd) (W : KdWf L)
    (hn : (L.dd A.codecs).noCalls = true) {i : Nat} (hi : i < L.k) {s : State} (h : DR L σ i 0 s) :
    WP isa (uHat L A i) s (DR L σ (i + 1) 0) := by
  obtain ⟨_, _, _, _, _, _, d5, _, _, r3, r4, _, _, _, _⟩ := id hp
  have hkt := h.kt
  have hk4 : L.k ≤ 4 := by rcases W.k34 with e | e <;> omega
  have bnd := Decaps.uSlice_le L hi
  have hct := W.ct
  have hdu := W.du
  have e1 := pa_r13 s hkt (32 * L.du * i)
  have e2 := pa_q s hkt i
  have H : DDHi wd (.r13, 32 * L.du * i) (qP i) L.du s :=
    { off := ⟨by omega, by simp only [oQ]; omega⟩
      dw := K.du.2
      dj := by rw [e1, e2]; exact (d5.sub_left (Offset.sub_base _ bnd)).sub_right (qScr (by omega))
      rB := by rw [retR_eq hkt, e1]; exact r3.sub_right (Offset.sub_base _ bnd)
      rF := by rw [retR_eq hkt, e2]; exact r4.sub_right (qScr (by omega))
      c := by
        rw [e1, e2]
        exact covers_append (covers_one (inT hp hkt bnd (by omega)))
          (covers_one (inC' hp hkt (by simp only [oQ, kScr]; omega)))
      w := by rw [e2]; exact covers_one (inC hp hkt (by simp only [oQ, kScr]; omega)) }
  refine WP.mono (ddIn_ok (K.dd A.codecs) hn (na_rbx _) H) fun s' ⟨hP, hq⟩ => ?_
  rw [e2] at hP hq
  obtain ⟨kt', hu, _⟩ := h.keep hp (i := i) (by omega) hk4 hP (.inl (Nat.le_refl _)) (by omega)
  refine ⟨kt', fun j hj => ?_, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  rcases (by omega : j < i ∨ j = i) with hj' | rfl
  · exact hu j hj'
  · rw [e1, ← bytesAt_slice _ _ bnd, hkt.bT] at hq
    exact hq

theorem s_ok {A : Arith} (hA : ArithOk A) (W : KdWf L) (hn : A.dec12.noCalls = true) {i : Nat} (hi : i < L.k)
    {s : State} (h : DR L σ L.k i s) : WP isa (sHat L A i) s (DR L σ L.k (i + 1)) := by
  obtain ⟨_, _, _, _, _, d4, _, _, r2, _, r4, _, _, _, _⟩ := id hp
  have hkt := h.kt
  have hk4 : L.k ≤ 4 := by rcases W.k34 with e | e <;> omega
  have bnd : 384 * i + 384 ≤ 384 * L.k := by omega
  have e1 := pa_rbp s hkt (384 * i)
  have e2 := pa_q s hkt (L.k + i)
  have H : TwoHi (.rbp, 384 * i) (qP (L.k + i)) 384 1024 s :=
    { off := ⟨by omega, by simp only [oQ]; omega⟩
      d := by rw [e1, e2]; exact (d4.sub_left (Offset.sub_base _ bnd)).sub_right (qScr (by omega))
      rP := by rw [retR_eq hkt, e1]; exact r2.sub_right (Offset.sub_base _ bnd)
      rQ := by rw [retR_eq hkt, e2]; exact r4.sub_right (qScr (by omega))
      c := by
        rw [e1, e2]
        exact covers_append (covers_one (inS hp hkt bnd (by omega)))
          (covers_one (inC' hp hkt (by simp only [oQ, kScr]; omega)))
      w := by rw [e2]; exact covers_one (inC hp hkt (by simp only [oQ, kScr]; omega)) }
  refine WP.mono (dec12In_ok hA.dec12.ok hn (na_rbx _) H) fun s' ⟨hP, hq⟩ => ?_
  rw [e2] at hP hq
  obtain ⟨kt', hu, hs⟩ := h.keep hp (i := L.k + i) (by omega) hk4 hP (.inr ⟨by omega, by omega, Nat.le_refl _⟩)
    (by omega)
  refine ⟨kt', hu, fun j hj => ?_⟩
  rcases (by omega : j < i ∨ j = i) with hj' | rfl
  · exact hs j hj' (by omega)
  · rw [e1, ← bytesAt_slice _ _ bnd, hkt.bS] at hq
    exact hq

/-! ## `m` -/

omit hp in
theorem q_add (k i : Nat) :
    σ.gpr .rcx + BitVec.ofNat 64 (oQ k) + BitVec.ofNat 64 (1024 * i) = σ.gpr .rcx + BitVec.ofNat 64 (oQ (k + i)) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  congr 2
  simp only [oQ]; omega

omit hp in
theorem vecAt_q (m : Mem) (k n : Nat) :
    vecAt m (σ.gpr .rcx + BitVec.ofNat 64 (oQ k)) n =
      (List.range n).map fun i => polyAt m (σ.gpr .rcx + BitVec.ofNat 64 (oQ (k + i))) := by
  simp only [vecAt, q_add]

/-- `KT` across code that writes only `m`. -/
theorem KT.stepM {s s' : State} (h : KT L σ s) (hP : IPost s s' [⟨σ.gpr .rdi + BitVec.ofNat 64 0, 32⟩]) :
    KT L σ s' := by
  obtain ⟨_, _, d1, d2, d3, _, _, r1, _, _, _, _, nS, nT, _⟩ := id hp
  rw [add_ofNat_zero] at hP
  have hd : ∀ (R : Region), R.Disjoint ⟨σ.gpr .rdi, 32⟩ → ∀ r ∈ [(⟨σ.gpr .rdi, 32⟩ : Region)], R.Disjoint r := by
    intro R hR r hr; rw [List.mem_singleton] at hr; subst hr; exact hR
  refine ⟨hP.rd.trans h.rd, hP.wr.trans h.wr, hP.rsp.trans h.rsp, (hP.cs .rbx (by decide)).trans h.rbx,
    (hP.cs .rbp (by decide)).trans h.rbp, (hP.cs .r12 (by decide)).trans h.r12, (hP.cs .r13 (by decide)).trans h.r13,
    (hP.cs .r14 (by decide)).trans h.r14, (hP.cs .r15 (by decide)).trans h.r15, fun i hi => ?_, ?_, ?_, ?_⟩
  · rw [hP.frame.readW (Region.contains_self _ _) (hd _ (d3.symm.sub_left (Offset.sub_base _
      (show oKS + 8 * i + 8 ≤ kScr by simp only [oKS, kScr]; omega)))) (by decide)]
    exact h.saved i hi
  · rw [hP.frame.readW (Region.contains_self _ _) (hd _ r1) (by decide)]; exact h.ret
  · rw [bytesAt_frame hP.frame (hd _ d1.symm) (by omega)]; exact h.bS
  · rw [bytesAt_frame hP.frame (hd _ d2.symm) (by omega)]; exact h.bT

/-- The rest of the function: the product, `v'`, `w` and `m`. -/
abbrev tail (L : Kem) (A : Arith) : Prog isa :=
  .seq (prod L A) (.seq (vHat L A) (.seq (wSub L A) (mOut L A)))

theorem tail_ok {A : Arith} (hA : ArithOk A) {wc wd : List Nat} (K : KemCalls L wc wd) (W : KdWf L)
    (hnM : (A.decMul L.k).noCalls = true) (hnD : (L.dd A.codecs).noCalls = true) (hnS : A.sub.noCalls = true)
    (hnC : A.codecs.ce.noCalls = true) {s : State} (h : DR L σ L.k L.k s) :
    WP isa (tail L A) s fun s' => KT L σ s' ∧
      bytesAt s'.mem (σ.gpr .rdi) 32 = kpkeDecrypt L.p (dB L σ) (cB L σ) := by
  obtain ⟨_, _, _, _, d3, _, d5, r1, _, r3, r4, _, _, _, _⟩ := id hp
  have hkt := h.kt
  have hk4 : L.k ≤ 4 := by rcases W.k34 with e | e <;> omega
  have hk0 : 0 < L.k := by rcases W.k34 with e | e <;> omega
  have hct := W.ct
  have hdu := W.du
  have hdv := W.dv
  have hq9 : ∀ i, i < 10 → oQ i + 1024 ≤ kScr := by intro i hi; simp only [oQ, kScr]; omega
  have sq : ∀ {a n : Nat}, a + n ≤ oTop → Region.Sub ⟨σ.gpr .rcx + BitVec.ofNat 64 a, n⟩ ⟨σ.gpr .rcx, kScr⟩ :=
    fun ha => fun x hx => sub_top x (Offset.sub_base _ ha x hx)
  have q0 : σ.gpr .rcx + BitVec.ofNat 64 (oQ 0) = σ.gpr .rcx + BitVec.ofNat 64 4096 := by simp [oQ]
  have od : ∀ {a n b m : Nat}, a + n ≤ b ∨ b + m ≤ a → a + n ≤ 2 ^ 64 → b + m ≤ 2 ^ 64 →
      Region.Disjoint ⟨σ.gpr .rcx + BitVec.ofNat 64 a, n⟩ ⟨σ.gpr .rcx + BitVec.ofNat 64 b, m⟩ :=
    fun h1 h2 h3 => Offset.disjoint _ h1 h2 h3
  -- the product
  have eW := pa_q s hkt (2 * L.k)
  have eS := pa_q s hkt L.k
  have eU := pa_q s hkt 0
  have eZ : pa s ((.rbx, 0) : Ptr) = σ.gpr .rcx + BitVec.ofNat 64 0 := by simp only [pa, hkt.rbx]
  have H : DecMulHi L.k (qP (2 * L.k)) (qP L.k) (qP 0) (.rbx, 0) s :=
    { off := ⟨by simp only [oQ]; omega, by simp only [oQ]; omega, by simp only [oQ]; omega, by omega⟩
      redS := by
        rw [eS]; intro i hi
        rw [q_add]; exact (h.sh i hi).1
      redU := by
        rw [eU]; intro i hi
        rw [q_add, Nat.zero_add]; exact (h.u i hi).1
      ws := by rw [eW, eS]; exact od (by simp only [oQ]; omega) (by simp only [oQ]; omega) (by simp only [oQ]; omega)
      wu := by rw [eW, eU]; exact od (by simp only [oQ]; omega) (by simp only [oQ]; omega) (by simp only [oQ]; omega)
      wz := by rw [eW, eZ]; exact od (by simp only [oQ]; omega) (by simp only [oQ]; omega) (by omega)
      sz := by rw [eS, eZ]; exact od (by simp only [oQ]; omega) (by simp only [oQ]; omega) (by omega)
      uz := by rw [eU, eZ]; exact od (by simp only [oQ]; omega) (by simp only [oQ]; omega) (by omega)
      rW := by rw [retR_eq hkt, eW]; exact r4.sub_right (sq (by simp only [oQ, oTop]; omega))
      rS := by rw [retR_eq hkt, eS]; exact r4.sub_right (sq (by simp only [oQ, oTop]; omega))
      rU := by rw [retR_eq hkt, eU]; exact r4.sub_right (sq (by simp only [oQ, oTop]; omega))
      rZ := by rw [retR_eq hkt, eZ]; exact r4.sub_right (sq (by simp only [oTop]; omega))
      c := by
        rw [eW, eS, eU, eZ]
        exact covers_append (covers_cons (covers_one (inC' hp hkt (by simp only [oQ, kScr]; omega)))
          (covers_cons (covers_one (inC' hp hkt (by simp only [oQ, kScr]; omega))) covers_nil))
          (covers_cons (covers_one (inC' hp hkt (by simp only [oQ, kScr]; omega)))
          (covers_cons (covers_one (inC' hp hkt (by simp only [kScr]; omega))) covers_nil))
      wc := by
        rw [eW, eZ]
        exact covers_cons (covers_one (inC hp hkt (by simp only [oQ, kScr]; omega)))
          (covers_cons (covers_one (inC hp hkt (by simp only [kScr]; omega))) covers_nil) }
  refine WP.seq (WP.mono (decMulIn_ok (hA.dm L.k W.k34).ok hnM (na_rbx _) (na_rbx _) (na_rbx _) H)
    fun s₁ ⟨hP₁, hq₁⟩ => ?_)
  rw [eW, eZ] at hP₁; rw [eW, eS, eU] at hq₁
  have kt₁ := hkt.step hp hP₁ (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.sub_base _ (by simp only [oQ, oTop]; omega)
    · exact Offset.sub_base _ (by simp only [oTop]; omega))
  have e1 : vecAt s.mem (σ.gpr .rcx + BitVec.ofNat 64 (oQ L.k)) L.k = (List.range L.k).map (dcS (dB L σ)) := by
    rw [vecAt_q]; exact List.map_congr_left fun i hi => (h.sh i (List.mem_range.mp hi)).2
  have e2 : (vecAt s.mem (σ.gpr .rcx + BitVec.ofNat 64 (oQ 0)) L.k).map ntt =
      (List.range L.k).map fun i => ntt (KPke.dcU L.p (cB L σ) i) := by
    rw [vecAt_q, List.map_map]
    exact List.map_congr_left fun i hi => by
      simp only [Function.comp, Nat.zero_add]; rw [(h.u i (List.mem_range.mp hi)).2]
  rw [e1, e2, KPke.dot_eq_dotK] at hq₁
  -- `v'`
  have bv : 32 * L.du * L.k + 32 * L.dv ≤ L.ctLen := by
    simp only [Kem.ctLen, Params.ctLen, Kem.du, Kem.dv, Kem.k]; rw [Nat.mul_add, ← Nat.mul_assoc]
  have eB := pa_r13 s₁ kt₁ (32 * L.du * L.k)
  have eV := pa_q s₁ kt₁ (2 * L.k + 1)
  have HV : DDHi wd (.r13, 32 * L.du * L.k) (qP (2 * L.k + 1)) L.dv s₁ :=
    { off := ⟨by omega, by simp only [oQ]; omega⟩
      dw := K.dv.2
      dj := by rw [eB, eV]; exact (d5.sub_left (Offset.sub_base _ bv)).sub_right (qScr (by omega))
      rB := by rw [retR_eq kt₁, eB]; exact r3.sub_right (Offset.sub_base _ bv)
      rF := by rw [retR_eq kt₁, eV]; exact r4.sub_right (qScr (by omega))
      c := by
        rw [eB, eV]
        exact covers_append (covers_one (inT hp kt₁ bv (by omega)))
          (covers_one (inC' hp kt₁ (hq9 _ (by omega))))
      w := by rw [eV]; exact covers_one (inC hp kt₁ (hq9 _ (by omega))) }
  refine WP.seq (WP.mono (ddIn_ok (K.dd A.codecs) hnD (na_rbx _) HV) fun s₂ ⟨hP₂, hq₂⟩ => ?_)
  rw [eV] at hP₂ hq₂
  rw [eB, ← bytesAt_slice _ _ bv, kt₁.bT] at hq₂
  have kt₂ := kt₁.step hp hP₂ (by
    intro r hr; rw [List.mem_singleton] at hr; subst hr; exact qSub (by omega))
  have hw₂ := polyIs_frame hP₂.frame (by
    intro r hr; rw [List.mem_singleton] at hr; subst hr; exact qDisj (by omega) (by omega) (by omega)) hq₁
  -- `w`
  have eF := pa_q s₂ kt₂ (2 * L.k + 1)
  have eG := pa_q s₂ kt₂ (2 * L.k)
  have HA : AccHi (qP (2 * L.k + 1)) (qP (2 * L.k)) s₂ :=
    { off := ⟨by simp only [oQ]; omega, by simp only [oQ]; omega⟩
      redF := by rw [eF]; exact hq₂.1
      redG := by rw [eG]; exact hw₂.1
      d := by rw [eF, eG]; exact qDisj (by omega) (by omega) (by omega)
      rF := by rw [retR_eq kt₂, eF]; exact r4.sub_right (qScr (by omega))
      rG := by rw [retR_eq kt₂, eG]; exact r4.sub_right (qScr (by omega))
      c := by
        rw [eF, eG]
        exact covers_append (covers_one (inC' hp kt₂ (hq9 _ (by omega))))
          (covers_one (inC' hp kt₂ (hq9 _ (by omega))))
      w := by rw [eF]; exact covers_one (inC hp kt₂ (hq9 _ (by omega))) }
  refine WP.seq (WP.mono (accIn_ok hA.sub.ok hnS (g := qP (2 * L.k)) (by simp) HA) fun s₃ ⟨hP₃, hq₃⟩ => ?_)
  rw [eF, eG, hq₂.2, hw₂.2] at hq₃
  rw [eF] at hP₃
  have kt₃ := kt₂.step hp hP₃ (by
    intro r hr; rw [List.mem_singleton] at hr; subst hr; exact qSub (by omega))
  -- `m`
  have eQ := pa_q s₃ kt₃ (2 * L.k + 1)
  have eM : pa s₃ ((.r12, 0) : Ptr) = σ.gpr .rdi + BitVec.ofNat 64 0 := by simp only [pa, kt₃.r12]
  have HC : CEHi compressWidths (qP (2 * L.k + 1)) (.r12, 0) 1 s₃ :=
    { off := ⟨by simp only [oQ]; omega, by omega⟩
      dw := by decide
      red := by rw [eQ]; exact hq₃.1
      dj := by
        rw [eQ, eM, add_ofNat_zero]
        exact (d3.symm.sub_left (qScr (by omega)))
      rF := by rw [retR_eq kt₃, eQ]; exact r4.sub_right (qScr (by omega))
      rO := by rw [retR_eq kt₃, eM, add_ofNat_zero]; exact r1
      c := by
        rw [eQ, eM]
        exact covers_append (covers_one (inC' hp kt₃ (hq9 _ (by omega))))
          (covers_one (by obtain ⟨r, hr, hc⟩ := inM hp kt₃; exact ⟨r, List.mem_append_right _ hr, hc⟩))
      w := by rw [eM]; exact covers_one (inM hp kt₃) }
  refine WP.mono (ceIn_ok (Codecs.ceI A.codecs) hnC (by decide) HC) fun s₄ ⟨hP₄, hq₄⟩ => ?_
  rw [eM] at hP₄ hq₄
  rw [eQ, hq₃.2] at hq₄
  refine ⟨kt₃.stepM hp hP₄, ?_⟩
  rw [← add_ofNat_zero (σ.gpr .rdi), hq₄, KPke.kpkeDecrypt_eq]
  rfl

end

/-! ## The function -/

theorem kpkeDec_wp {L : Kem} {A : Arith} (hA : ArithOk A) {wc wd : List Nat} (K : KemCalls L wc wd)
    (W : KdWf L) (hnD : (L.dd A.codecs).noCalls = true) (hn12 : A.dec12.noCalls = true)
    (hnM : (A.decMul L.k).noCalls = true) (hnS : A.sub.noCalls = true) (hnC : A.codecs.ce.noCalls = true)
    {σ : State} (hp : (kpkeDecK L).pre σ) :
    WP isa (kpkeDec L A) σ fun s' => gprPreserved σ s' ∧ (kpkeDecK L).post σ s' := by
  refine WP.seq (WP.mono (pro_ok hp) fun s₁ h₁ => ?_)
  have d₀ : DR L σ 0 0 s₁ := ⟨h₁, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  refine WP.seq ?_
  unfold decBody
  refine WP.seq (WP.mono (seqR_ok (I := fun i s => DR L σ i 0 s) L.k 0
    (fun i _ hi s h => u_ok hp K W hnD (by omega) h) s₁ d₀) fun s₂ h₂ => ?_)
  rw [Nat.zero_add] at h₂
  have d₂ : DR L σ L.k 0 s₂ := h₂
  refine WP.seq (WP.mono (seqR_ok (I := fun i s => DR L σ L.k i s) L.k 0
    (fun i _ hi s h => s_ok hp hA W hn12 (by omega) h) s₂ d₂) fun s₃ h₃ => ?_)
  rw [Nat.zero_add] at h₃
  exact WP.mono (tail_ok hp hA K W hnM hnD hnS hnC h₃) fun s₄ ⟨kt₄, hm₄⟩ =>
    WP.mono (epi_ok hp kt₄) fun s₅ ⟨hg, hm⟩ => ⟨hg, by show bytesAt _ _ _ = _; rw [hm]; exact hm₄⟩

theorem kpkeDec_correct {L : Kem} {A : Arith} (hA : ArithOk A) {wc wd : List Nat} (K : KemCalls L wc wd)
    (W : KdWf L) (hnD : (L.dd A.codecs).noCalls = true) (hn12 : A.dec12.noCalls = true)
    (hnM : (A.decMul L.k).noCalls = true) (hnS : A.sub.noCalls = true) (hnC : A.codecs.ce.noCalls = true)
    (hctl : ctlOk (kpkeDec L A) = true) (σ : State) (hp : (kpkeDecK L).pre σ) :
    ∃ t s', Exec isa (kpkeDec L A) σ t s' ∧ abiPreserved σ s' ∧ (kpkeDecK L).post σ s' := by
  obtain ⟨t, s', he, hg, hq⟩ := kpkeDec_wp hA K W hnD hn12 hnM hnS hnC hp
  exact ⟨t, s', he, abiPreserved_of_ctl hctl he hg, hq⟩

end KpkeDec

end VG.Proof.MlKem.X86_64

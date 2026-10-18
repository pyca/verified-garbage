module

public import VerifiedGarbage.Proof.MlKem.X86_64.KpkeEnc
public import VerifiedGarbage.Proof.MlKem.X86_64.KgMul
import VerifiedGarbage.Proof.MlKem.X86_64.FragPrim

/-!
# ML-KEM on x86-64: `vg_mlkem*_kpke_keygen`

The contract (`kpkeKgK`), what holds throughout the function (`KT`: the
pointers, the saved registers, and that only `scratch`, `ek` and `dk`
change), and the steps: the prologue, `s` and `e` as `u32`s (`widenIn_ok`),
the products (the code of `vg_mlkem*_keygen_mul` reading `Â` as `u16`s,
inline), `ByteEncode₁₂` of `t̂` to `ek` and of `ŝ` to `dk` (`enc12In_ok`), and
the epilogue.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- `vg_mlkem*_kpke_keygen(ek = rdi, dk = rsi, a = rdx, se = rcx, scratch = r8)` of the parameter set `L`. -/
def kpkeKgK (L : Kem) : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdx, 512 * (L.k * L.k)⟩] ∧
    s.wr = [⟨s.gpr .rdi, 384 * L.k⟩, ⟨s.gpr .rsi, 384 * L.k⟩, ⟨s.gpr .rcx, 1024 * L.k⟩, ⟨s.gpr .r8, kScrE⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, 384 * L.k⟩ ⟨s.gpr .rsi, 384 * L.k⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, 384 * L.k⟩ ⟨s.gpr .rdx, 512 * (L.k * L.k)⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, 384 * L.k⟩ ⟨s.gpr .rcx, 1024 * L.k⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, 384 * L.k⟩ ⟨s.gpr .r8, kScrE⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, 384 * L.k⟩ ⟨s.gpr .rdx, 512 * (L.k * L.k)⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, 384 * L.k⟩ ⟨s.gpr .rcx, 1024 * L.k⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, 384 * L.k⟩ ⟨s.gpr .r8, kScrE⟩ ∧
    Region.Disjoint ⟨s.gpr .rdx, 512 * (L.k * L.k)⟩ ⟨s.gpr .rcx, 1024 * L.k⟩ ∧
    Region.Disjoint ⟨s.gpr .rdx, 512 * (L.k * L.k)⟩ ⟨s.gpr .r8, kScrE⟩ ∧
    Region.Disjoint ⟨s.gpr .rcx, 1024 * L.k⟩ ⟨s.gpr .r8, kScrE⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, 384 * L.k⟩ ∧ (retR s).Disjoint ⟨s.gpr .rsi, 384 * L.k⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdx, 512 * (L.k * L.k)⟩ ∧ (retR s).Disjoint ⟨s.gpr .rcx, 1024 * L.k⟩ ∧
    (retR s).Disjoint ⟨s.gpr .r8, kScrE⟩ ∧
    (s.gpr .rdi).toNat + 384 * L.k ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 384 * L.k ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + 512 * (L.k * L.k) ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 1024 * L.k ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + kScrE ≤ 2 ^ 64 ∧
    VecReducedW 16 s.mem (s.gpr .rdx) (L.k * L.k) ∧ VecReducedW 16 s.mem (s.gpr .rcx) (2 * L.k)
  post s s' :=
    let ŝ := (vecAtW 16 s.mem (s.gpr .rcx) L.k).map ntt
    let ê := (vecAtW 16 s.mem (s.gpr .rcx + BitVec.ofNat 64 (512 * L.k)) L.k).map ntt
    bytesAt s'.mem (s.gpr .rdi) (384 * L.k) = encodeVec (addVec (mulMatVec (matAtW 16 s.mem (s.gpr .rdx) L.k) ŝ) ê) ∧
      bytesAt s'.mem (s.gpr .rsi) (384 * L.k) = encodeVec ŝ
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-! ## `ByteEncode₁₂` inline -/

theorem enc12In_ok {c : Prog isa} (hv : ∀ s, encode12K.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧
      encode12K.post s s') (hn : c.noCalls = true) {p q : Ptr} (hq : NA q) {s : State} (h : TwoHi p q 1024 384 s)
    (hr : Reduced s.mem (pa s p)) :
    WP isa (.seq (.block (lea .rdi p ++ lea .rsi q)) c) s fun s' => IPost s s' [⟨pa s q, 384⟩] ∧
      bytesAt s'.mem (pa s q) 384 = encode12 (polyAt s.mem (pa s p)) := by
  have hq1 : q.1 ≠ .rdi := fun e => hq (by rw [e]; decide)
  refine WP.mono (glueIn_ok hv hn (accGlue_ok p q h.off.1 h.off.2 hq1 s) (rd := [pR (pa s p)])
    (wr := [⟨pa s q, 384⟩])
    (fun s1 hv hm k => by
      simp only [encode12K, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
        hv.1, hv.2, hm]
      exact ⟨trivial, trivial, h.d, retR_keep k h.rP _ _, retR_keep k h.rQ _ _, hr⟩) h.c h.w)
    fun s' ⟨hpost, s1, hV, hm, _, hq⟩ => ⟨hpost, ?_⟩
  simp only [encode12K, State.withRegions_gpr, State.withRegions_mem, hV.1, hV.2, hm] at hq
  exact hq

namespace KpkeKg

open VG.Impl.MlKem.X86_64.Kpke16
open KpkeEnc (oTop sub_top flatMap_congr list_eq_map_getD bytesAt_cat off_add na_rbx)

/-- The facts of the precondition, by name. -/
structure EP (L : Kem) (σ : State) : Prop where
  rd : σ.rd = [⟨σ.gpr .rdx, 512 * (L.k * L.k)⟩]
  wr : σ.wr = [⟨σ.gpr .rdi, 384 * L.k⟩, ⟨σ.gpr .rsi, 384 * L.k⟩, ⟨σ.gpr .rcx, 1024 * L.k⟩, ⟨σ.gpr .r8, kScrE⟩]
  cD : Region.Disjoint ⟨σ.gpr .rdi, 384 * L.k⟩ ⟨σ.gpr .rsi, 384 * L.k⟩
  cA : Region.Disjoint ⟨σ.gpr .rdi, 384 * L.k⟩ ⟨σ.gpr .rdx, 512 * (L.k * L.k)⟩
  cS : Region.Disjoint ⟨σ.gpr .rdi, 384 * L.k⟩ ⟨σ.gpr .rcx, 1024 * L.k⟩
  cX : Region.Disjoint ⟨σ.gpr .rdi, 384 * L.k⟩ ⟨σ.gpr .r8, kScrE⟩
  dA : Region.Disjoint ⟨σ.gpr .rsi, 384 * L.k⟩ ⟨σ.gpr .rdx, 512 * (L.k * L.k)⟩
  dS : Region.Disjoint ⟨σ.gpr .rsi, 384 * L.k⟩ ⟨σ.gpr .rcx, 1024 * L.k⟩
  dX : Region.Disjoint ⟨σ.gpr .rsi, 384 * L.k⟩ ⟨σ.gpr .r8, kScrE⟩
  aS : Region.Disjoint ⟨σ.gpr .rdx, 512 * (L.k * L.k)⟩ ⟨σ.gpr .rcx, 1024 * L.k⟩
  aX : Region.Disjoint ⟨σ.gpr .rdx, 512 * (L.k * L.k)⟩ ⟨σ.gpr .r8, kScrE⟩
  sX : Region.Disjoint ⟨σ.gpr .rcx, 1024 * L.k⟩ ⟨σ.gpr .r8, kScrE⟩
  xC : (retR σ).Disjoint ⟨σ.gpr .rdi, 384 * L.k⟩
  xD : (retR σ).Disjoint ⟨σ.gpr .rsi, 384 * L.k⟩
  xA : (retR σ).Disjoint ⟨σ.gpr .rdx, 512 * (L.k * L.k)⟩
  xS : (retR σ).Disjoint ⟨σ.gpr .rcx, 1024 * L.k⟩
  xX : (retR σ).Disjoint ⟨σ.gpr .r8, kScrE⟩
  nC : (σ.gpr .rdi).toNat + 384 * L.k ≤ 2 ^ 64
  nD : (σ.gpr .rsi).toNat + 384 * L.k ≤ 2 ^ 64
  nA : (σ.gpr .rdx).toNat + 512 * (L.k * L.k) ≤ 2 ^ 64
  nS : (σ.gpr .rcx).toNat + 1024 * L.k ≤ 2 ^ 64
  nX : (σ.gpr .r8).toNat + kScrE ≤ 2 ^ 64
  redA : VecReducedW 16 σ.mem (σ.gpr .rdx) (L.k * L.k)
  redS : VecReducedW 16 σ.mem (σ.gpr .rcx) (2 * L.k)

theorem ep {L : Kem} {σ : State} (hp : (kpkeKgK L).pre σ) : EP L σ :=
  let ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
    h23⟩ := hp
  ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩

/-- The regions of `σ` that the function may change. -/
abbrev chg (L : Kem) (σ : State) : List Region :=
  [⟨σ.gpr .r8, kScrE⟩, ⟨σ.gpr .rdi, 384 * L.k⟩, ⟨σ.gpr .rsi, 384 * L.k⟩]

/-- What holds throughout the function entered in `σ`. -/
structure KT (L : Kem) (σ s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  rsp : s.gpr .rsp = σ.gpr .rsp
  rbx : s.gpr .rbx = σ.gpr .r8
  rbp : s.gpr .rbp = σ.gpr .rsi
  r12 : s.gpr .r12 = σ.gpr .rdx
  r13 : s.gpr .r13 = σ.gpr .rcx
  r15 : s.gpr .r15 = σ.gpr .rdi
  saved : ∀ i < 6, s.mem.readW (σ.gpr .r8 + BitVec.ofNat 64 (oKSE + 8 * i)) 64 = σ.gpr (kRegs.getD i .rbx)
  ret : s.mem.readW (σ.gpr .rsp) 64 = σ.mem.readW (σ.gpr .rsp) 64
  fr : Frame (chg L σ) σ.mem s.mem

section
variable {L : Kem} {σ : State} (E : EP L σ)
include E

omit E in
theorem sub_topG : Region.Sub ⟨σ.gpr .r8, oTop⟩ ⟨σ.gpr .r8, kScrE⟩ := Region.sub_prefix (by decide)

/-- A region the steps write: below `oTop` in `scratch`, or in `ek` or `dk`. -/
abbrev WOk (L : Kem) (σ : State) (r : Region) : Prop :=
  Region.Sub r ⟨σ.gpr .r8, oTop⟩ ∨ Region.Sub r ⟨σ.gpr .rdi, 384 * L.k⟩ ∨ Region.Sub r ⟨σ.gpr .rsi, 384 * L.k⟩

theorem wok_disj {r : Region} (hr : WOk L σ r) :
    (retR σ).Disjoint r ∧ ∀ i < 6, Region.Disjoint ⟨σ.gpr .r8 + BitVec.ofNat 64 (oKSE + 8 * i), 8⟩ r := by
  have hs : ∀ i < 6, Region.Sub ⟨σ.gpr .r8 + BitVec.ofNat 64 (oKSE + 8 * i), 8⟩ ⟨σ.gpr .r8, kScrE⟩ := fun i hi =>
    Offset.sub_base _ (by simp only [oKSE, kScrE]; omega)
  rcases hr with hr | hr | hr
  · refine ⟨(E.xX.sub_right sub_topG).sub_right hr, fun i hi => ?_⟩
    exact (Offset.disjoint_base (σ.gpr .r8) (d := oKSE + 8 * i) (n := 8) (k := oTop)
      (by simp only [oKSE, oTop]; omega) (by have := E.nX; simp only [oKSE, kScrE] at *; omega)).sub_right hr
  · exact ⟨E.xC.sub_right hr, fun i hi => (E.cX.symm.sub_left (hs i hi)).sub_right hr⟩
  · exact ⟨E.xD.sub_right hr, fun i hi => (E.dX.symm.sub_left (hs i hi)).sub_right hr⟩

omit E in
theorem wok_chg {r : Region} (hr : WOk L σ r) : ∃ r' ∈ chg L σ, Region.Sub r r' := by
  rcases hr with hr | hr | hr
  · exact ⟨_, List.mem_cons_self .., fun x hx => sub_topG x (hr x hx)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), hr⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), hr⟩

theorem KT.stepF {s s' : State} (h : KT L σ s) {W : List Region} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.gpr .rsp = s.gpr .rsp) (hcs : ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r15], s'.gpr r = s.gpr r)
    (hf : Frame W s.mem s'.mem) (hW : ∀ r ∈ W, WOk L σ r) : KT L σ s' := by
  have D := fun r hr => wok_disj E (r := r) (hW r hr)
  refine ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.rsp, (hcs .rbx (by simp)).trans h.rbx,
    (hcs .rbp (by simp)).trans h.rbp, (hcs .r12 (by simp)).trans h.r12, (hcs .r13 (by simp)).trans h.r13,
    (hcs .r15 (by simp)).trans h.r15, fun i hi => ?_, ?_, h.fr.trans (hf.sub fun r hr => wok_chg (hW r hr))⟩
  · rw [hf.readW (Region.contains_self _ _) (fun r hr => (D r hr).2 i hi) (by decide)]
    exact h.saved i hi
  · rw [hf.readW (Region.contains_self _ _) (fun r hr => (D r hr).1) (by decide)]
    exact h.ret

theorem KT.step {s s' : State} (h : KT L σ s) {W : List Region} (hP : IPost s s' W)
    (hW : ∀ r ∈ W, WOk L σ r) : KT L σ s' :=
  h.stepF E hP.rd hP.wr hP.rsp (fun r hr => hP.cs r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)) hP.frame hW

/-- Polynomial `j` of `se` (`u16`s), as on entry. -/
theorem KT.rW {s : State} (h : KT L σ s) {j : Nat} (hj : j < 2 * L.k) :
    PolyIsW 16 s.mem (σ.gpr .rcx + BitVec.ofNat 64 (512 * j)) (KpkeEnc.rW σ j) := by
  have hs : Region.Sub ⟨σ.gpr .rcx + BitVec.ofNat 64 (512 * j), 512⟩ ⟨σ.gpr .rcx, 1024 * L.k⟩ :=
    Offset.sub_base _ (by omega)
  refine polyIsW16_frame h.fr (fun r hr => ?_) ⟨?_, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [E.sX.sub_left hs, E.cS.symm.sub_left hs, E.dS.symm.sub_left hs]
  · have := E.redS j hj
    rwa [show 32 * 16 * j = 512 * j by omega] at this

/-- Polynomial `e` of `a` (`u16`s), as on entry. -/
theorem KT.aW {s : State} (h : KT L σ s) {e : Nat} (he : e < L.k * L.k) :
    PolyIsW 16 s.mem (σ.gpr .rdx + BitVec.ofNat 64 (512 * e))
      (polyAtW 16 σ.mem (σ.gpr .rdx + BitVec.ofNat 64 (512 * e))) := by
  have hs : Region.Sub ⟨σ.gpr .rdx + BitVec.ofNat 64 (512 * e), 512⟩ ⟨σ.gpr .rdx, 512 * (L.k * L.k)⟩ :=
    Offset.sub_base _ (by omega)
  refine polyIsW16_frame h.fr (fun r hr => ?_) ⟨?_, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [E.aX.sub_left hs, E.cA.symm.sub_left hs, E.dA.symm.sub_left hs]
  · have := E.redA e he
    rwa [show 32 * 16 * e = 512 * e by omega] at this

theorem KT.mat {s : State} (h : KT L σ s) :
    matAtW 16 s.mem (σ.gpr .rdx) L.k = matAtW 16 σ.mem (σ.gpr .rdx) L.k := by
  simp only [matAtW, vecAtW]
  refine List.map_congr_left fun i hi => List.map_congr_left fun j hj => ?_
  have hi := List.mem_range.mp hi
  have hj := List.mem_range.mp hj
  have he : L.k * i + j < L.k * L.k :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj _) (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi)
  rw [off_add, show 32 * 16 * (L.k * i) + 32 * 16 * j = 512 * (L.k * i + j) by omega]
  exact (h.aW E he).2

/-! ## The prologue and the epilogue -/

omit E in
theorem proG_eq : proG = [.store (at_ .r8 19456) .rbx, .store (at_ .r8 19464) .rbp, .store (at_ .r8 19472) .r12,
    .store (at_ .r8 19480) .r13, .store (at_ .r8 19488) .r14, .store (at_ .r8 19496) .r15,
    .mov .rbx (.reg .r8), .mov .r15 (.reg .rdi), .mov .rbp (.reg .rsi), .mov .r12 (.reg .rdx),
    .mov .r13 (.reg .rcx)] := rfl

theorem pro_ok : WP isa (.block proG) σ (KT L σ) := by
  have hS : ⟨σ.gpr .r8, kScrE⟩ ∈ σ.wr := by rw [E.wr]; simp
  have nX := E.nX
  have c : ∀ o, o + 8 ≤ kScrE → (⟨σ.gpr .r8, kScrE⟩ : Region).Contains (σ.gpr .r8 + BitVec.ofNat 64 o) 8 :=
    fun o ho => Offset.contains_base _ ho (by omega)
  have w : ∀ o, o + 8 ≤ kScrE → InRegions σ.wr (σ.gpr .r8 + BitVec.ofNat 64 o) 8 := fun o ho => ⟨_, hS, c o ho⟩
  have w0 := w 19456 (by decide); have w1 := w 19464 (by decide); have w2 := w 19472 (by decide)
  have w3 := w 19480 (by decide); have w4 := w 19488 (by decide); have w5 := w 19496 (by decide)
  rw [proG_eq]
  refine WP.mono (WP.keep [.rbx, .r15, .rbp, .r12, .r13] (Q := fun s =>
    s.mem = (((((σ.mem.writeW (σ.gpr .r8 + BitVec.ofNat 64 19456) (σ.gpr .rbx)).writeW
      (σ.gpr .r8 + BitVec.ofNat 64 19464) (σ.gpr .rbp)).writeW (σ.gpr .r8 + BitVec.ofNat 64 19472) (σ.gpr .r12)).writeW
      (σ.gpr .r8 + BitVec.ofNat 64 19480) (σ.gpr .r13)).writeW (σ.gpr .r8 + BitVec.ofNat 64 19488) (σ.gpr .r14)).writeW
      (σ.gpr .r8 + BitVec.ofNat 64 19496) (σ.gpr .r15) ∧
    s.gpr .rbx = σ.gpr .r8 ∧ s.gpr .r15 = σ.gpr .rdi ∧ s.gpr .rbp = σ.gpr .rsi ∧ s.gpr .r12 = σ.gpr .rdx ∧
    s.gpr .r13 = σ.gpr .rcx)
    (by xrun [w0, w1, w2, w3, w4, w5]) (by decide)) fun s ⟨⟨hm, hbx, h15, hbp, h12, h13⟩, k⟩ => ?_
  have hf : Frame [⟨σ.gpr .r8, kScrE⟩] σ.mem s.mem := by
    rw [hm]
    exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 19456 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 19464 (by decide))).writeW (List.mem_singleton_self _) _
      (c 19472 (by decide))).writeW (List.mem_singleton_self _) _ (c 19480 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 19488 (by decide))).writeW (List.mem_singleton_self _) _ (c 19496 (by decide)))
  refine ⟨k.2.1, k.2.2, k.gpr (by decide), hbx, hbp, h12, h13, h15, fun i hi => ?_, ?_, hf.mono (by simp)⟩
  · rw [hm]
    exact KpkeEnc.stores_read σ.mem (σ.gpr .r8) (fun i => σ.gpr (kRegs.getD i .rbx)) i hi
  · exact hf.readW (Region.contains_self _ _) (by simpa using E.xX) (by decide)

theorem epi_ok {s : State} (h : KT L σ s) :
    WP isa (.block epiE) s fun s' => gprPreserved σ s' ∧ s'.mem = s.mem := by
  have nX := E.nX
  have hS : ⟨σ.gpr .r8, kScrE⟩ ∈ s.wr := by rw [h.wr, E.wr]; simp
  have i : ∀ j < 6, InRegions (s.rd ++ s.wr) (s.gpr .rbx + BitVec.ofNat 64 (oKSE + 8 * j)) 8 := fun j hj =>
    ⟨_, List.mem_append_right _ hS, by
      rw [h.rbx]; exact Offset.contains_base _ (by simp only [oKSE, kScrE]; omega) (by simp only [oKSE]; omega)⟩
  have e : ∀ j < 6, s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 (oKSE + 8 * j)) 64 = σ.gpr (kRegs.getD j .rbx) :=
    fun j hj => by rw [h.rbx]; exact h.saved j hj
  have e0 := e 0 (by decide); have e1 := e 1 (by decide); have e2 := e 2 (by decide); have e3 := e 3 (by decide)
  have e4 := e 4 (by decide); have e5 := e 5 (by decide)
  have i0 := i 0 (by decide); have i1 := i 1 (by decide); have i2 := i 2 (by decide); have i3 := i 3 (by decide)
  have i4 := i 4 (by decide); have i5 := i 5 (by decide)
  simp only [oKSE, kRegs, List.getD_cons_zero, List.getD_cons_succ, Nat.reduceMul, Nat.reduceAdd]
    at e0 e1 e2 e3 e4 e5 i0 i1 i2 i3 i4 i5
  rw [KpkeEnc.epiE_eq]
  refine WP.mono (WP.keep [.r15, .r14, .r13, .r12, .rbp, .rbx] (Q := fun s' =>
    s'.gpr .r15 = σ.gpr .r15 ∧ s'.gpr .r14 = σ.gpr .r14 ∧ s'.gpr .r13 = σ.gpr .r13 ∧ s'.gpr .r12 = σ.gpr .r12 ∧
    s'.gpr .rbp = σ.gpr .rbp ∧ s'.gpr .rbx = σ.gpr .rbx ∧ s'.mem = s.mem)
    (by xrun [i0, i1, i2, i3, i4, i5, e0, e1, e2, e3, e4, e5]) (by decide))
    fun s' ⟨⟨h15, h14, h13, h12, hbp, hbx, hm⟩, k⟩ => ⟨⟨fun r hr => ?_, ?_⟩, hm⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hbx, hbp, by rw [k.gpr (by decide), h.rsp], h12, h13, h14, h15]
  · rw [hm]; exact h.ret

/-! ## Regions -/

section
variable {s : State} (h : KT L σ s)
include h

theorem inS {o n : Nat} (ho : o + n ≤ kScrE) : InRegions s.wr (σ.gpr .r8 + BitVec.ofNat 64 o) n :=
  ⟨_, by rw [h.wr, E.wr]; simp, Offset.contains_base _ ho (by have := E.nX; simp only [kScrE] at *; omega)⟩

theorem inS' {o n : Nat} (ho : o + n ≤ kScrE) : InRegions (s.rd ++ s.wr) (σ.gpr .r8 + BitVec.ofNat 64 o) n := by
  obtain ⟨r, hr, hc⟩ := inS E h ho
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem inEk {o n : Nat} (ho : o + n ≤ 384 * L.k) (hn : 0 < n) :
    InRegions s.wr (σ.gpr .rdi + BitVec.ofNat 64 o) n :=
  ⟨_, by rw [h.wr, E.wr]; simp, Offset.contains_base _ ho (by have := E.nC; omega)⟩

theorem inDk {o n : Nat} (ho : o + n ≤ 384 * L.k) (hn : 0 < n) :
    InRegions s.wr (σ.gpr .rsi + BitVec.ofNat 64 o) n :=
  ⟨_, by rw [h.wr, E.wr]; simp, Offset.contains_base _ ho (by have := E.nD; omega)⟩

theorem inR {o n : Nat} (ho : o + n ≤ 1024 * L.k) (hn : 0 < n) :
    InRegions (s.rd ++ s.wr) (σ.gpr .rcx + BitVec.ofNat 64 o) n :=
  ⟨_, List.mem_append_right _ (by rw [h.wr, E.wr]; simp), Offset.contains_base _ ho (by have := E.nS; omega)⟩

theorem inA {o n : Nat} (ho : o + n ≤ 512 * (L.k * L.k)) (hn : 0 < n) :
    InRegions (s.rd ++ s.wr) (σ.gpr .rdx + BitVec.ofNat 64 o) n :=
  ⟨_, List.mem_append_left _ (by rw [h.rd, E.rd]; simp), Offset.contains_base _ ho (by have := E.nA; omega)⟩

omit E in
theorem retR_eq : retR s = retR σ := by simp only [retR, h.rsp]

omit E in
theorem pa_q (i : Nat) : pa s (qP i) = σ.gpr .r8 + BitVec.ofNat 64 (oQ i) := by simp only [pa, h.rbx]

end

omit E in
theorem qSub {i : Nat} (hi : i < 14) :
    Region.Sub (pR (σ.gpr .r8 + BitVec.ofNat 64 (oQ i))) ⟨σ.gpr .r8, oTop⟩ :=
  Offset.sub_base _ (by simp only [oQ, oTop]; omega)

omit E in
theorem qScr {i : Nat} (hi : i < 14) :
    Region.Sub (pR (σ.gpr .r8 + BitVec.ofNat 64 (oQ i))) ⟨σ.gpr .r8, kScrE⟩ :=
  fun x hx => sub_topG x (qSub hi x hx)

theorem qDisj {i j : Nat} (hi : i < 14) (hj : j < 14) (hij : i ≠ j) :
    (pR (σ.gpr .r8 + BitVec.ofNat 64 (oQ i))).Disjoint (pR (σ.gpr .r8 + BitVec.ofNat 64 (oQ j))) :=
  Offset.disjoint _ (by simp only [oQ]; omega) (by have := E.nX; simp only [oQ, kScrE] at *; omega)
    (by have := E.nX; simp only [oQ, kScrE] at *; omega)

omit E in
theorem q_add (b i : Nat) :
    σ.gpr .r8 + BitVec.ofNat 64 (oQ b) + BitVec.ofNat 64 (1024 * i) = σ.gpr .r8 + BitVec.ofNat 64 (oQ (b + i)) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  congr 2
  simp only [oQ]; omega

/-! ## `s` and `e` -/

/-- The first `ny` of `s` are done, as `u32`s. -/
structure ER (L : Kem) (σ : State) (ny : Nat) (s : State) : Prop where
  kt : KT L σ s
  y : ∀ j < ny, PolyIs s.mem (σ.gpr .r8 + BitVec.ofNat 64 (oQ j)) (KpkeEnc.rW σ j)

theorem y_ok (W : KpkeEnc.KeWf L) {j : Nat} (hj : j < L.k) {s : State} (h : ER L σ j s) :
    WP isa (yE j) s (ER L σ (j + 1)) := by
  have hkt := h.kt
  have hk4 : L.k ≤ 4 := by rcases W.k34 with e | e <;> omega
  have bnd : 512 * j + 512 ≤ 1024 * L.k := by omega
  have e1 : pa s ((.r13, 512 * j) : Ptr) = σ.gpr .rcx + BitVec.ofNat 64 (512 * j) := by simp only [pa, hkt.r13]
  have e2 := pa_q hkt j
  refine WP.mono (widenIn_ok (b := (.r13, 512 * j)) (f := qP j) (F := KpkeEnc.rW σ j) (by omega)
    (by simp only [oQ]; omega) (by simp)
    (by rw [e1]; exact hkt.rW E (by omega))
    (by rw [e1, e2]; exact (E.sX.symm.sub_left (qScr (by omega))).sub_right (Offset.sub_base _ bnd))
    (by rw [e1, e2]
        exact covers_append (covers_one (inR E hkt bnd (by omega)))
          (covers_one (inS' E hkt (by simp only [oQ, kScrE]; omega))))
    (by rw [e2]; exact covers_one (inS E hkt (by simp only [oQ, kScrE]; omega)))) fun s' ⟨hP, hq⟩ => ?_
  rw [e2] at hP hq
  refine ⟨hkt.step E hP fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact .inl (qSub (by omega)),
    fun j' hj' => ?_⟩
  rcases (by omega : j' < j ∨ j' = j) with hj'' | rfl
  · exact polyIs_frame hP.frame (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact qDisj E (by omega) (by omega) (by omega)) (h.y j' hj'')
  · exact hq

/-! ## The products -/

/-- `ŝ`, from `s` on entry. -/
abbrev sHat (L : Kem) (σ : State) : List Poly := (vecAtW 16 σ.mem (σ.gpr .rcx) L.k).map ntt

/-- `ê`, from `e` on entry. -/
abbrev eHat (L : Kem) (σ : State) : List Poly :=
  (vecAtW 16 σ.mem (σ.gpr .rcx + BitVec.ofNat 64 (512 * L.k)) L.k).map ntt

/-- `t̂ = Â ∘ ŝ + ê`, from the inputs on entry. -/
abbrev tHat (L : Kem) (σ : State) : List Poly :=
  addVec (mulMatVec (matAtW 16 σ.mem (σ.gpr .rdx) L.k) (sHat L σ)) (eHat L σ)

/-- After the products: the first `nt` of `t̂` are in `ek` and `ns` of `ŝ` in `dk`, the others in place. -/
structure EO (L : Kem) (σ : State) (nt ns : Nat) (s : State) : Prop where
  kt : KT L σ s
  t : ∀ i < L.k, nt ≤ i → PolyIs s.mem (σ.gpr .r8 + BitVec.ofNat 64 (oQ (2 * L.k + i))) ((tHat L σ).getD i zero)
  sh : ∀ j < L.k, ns ≤ j → PolyIs s.mem (σ.gpr .r8 + BitVec.ofNat 64 (oQ j)) ((sHat L σ).getD j zero)
  ek : ∀ i < nt, bytesAt s.mem (σ.gpr .rdi + BitVec.ofNat 64 (384 * i)) 384 = encode12 ((tHat L σ).getD i zero)
  dk : ∀ j < ns, bytesAt s.mem (σ.gpr .rsi + BitVec.ofNat 64 (384 * j)) 384 = encode12 ((sHat L σ).getD j zero)

theorem mul_ok (W : KpkeEnc.KeWf L) {mul : Nat → Prog isa}
    (hv : ∀ s, (kgMulK16 L.k).pre s → ∃ t s', Exec isa (mul L.k) s t s' ∧ abiPreserved s s' ∧
      (kgMulK16 L.k).post s s')
    (hn : (mul L.k).noCalls = true) {s : State} (h : ER L σ L.k s) :
    WP isa (prodG L mul) s (EO L σ 0 0) := by
  have hkt := h.kt
  have hk4 : L.k ≤ 4 := by rcases W.k34 with e | e <;> omega
  have hkk : 0 < 512 * (L.k * L.k) := by rcases W.k34 with e | e <;> rw [e] <;> decide
  have eU := pa_q hkt (2 * L.k)
  have eE : pa s ((.r13, 512 * L.k) : Ptr) = σ.gpr .rcx + BitVec.ofNat 64 (512 * L.k) := by simp only [pa, hkt.r13]
  have sE : Region.Sub ⟨σ.gpr .rcx + BitVec.ofNat 64 (512 * L.k), 512 * L.k⟩ ⟨σ.gpr .rcx, 1024 * L.k⟩ :=
    Offset.sub_base _ (by omega)
  have eS := pa_q hkt 0
  have eA : pa s ((.r12, 0) : Ptr) = σ.gpr .rdx := by simp only [pa, hkt.r12, add_ofNat_zero]
  have eZ : pa s ((.rbx, 0) : Ptr) = σ.gpr .r8 := by simp only [pa, hkt.rbx, add_ofNat_zero]
  have od : ∀ {a n b m : Nat}, a + n ≤ b ∨ b + m ≤ a → a + n ≤ kScrE → b + m ≤ kScrE →
      Region.Disjoint ⟨σ.gpr .r8 + BitVec.ofNat 64 a, n⟩ ⟨σ.gpr .r8 + BitVec.ofNat 64 b, m⟩ := by
    have nX := E.nX
    exact fun {a n b m} h1 h2 h3 => Offset.disjoint _ h1 (by simp only [kScrE] at h2; omega) (by simp only [kScrE] at h3; omega)
  have od0 : ∀ {a n : Nat}, 4096 ≤ a → a + n ≤ kScrE →
      Region.Disjoint ⟨σ.gpr .r8 + BitVec.ofNat 64 a, n⟩ (cR (σ.gpr .r8)) := fun {a n} h1 h2 => by
    have := od (a := a) (n := n) (b := 0) (m := 4096) (.inr h1) h2 (by decide)
    rwa [add_ofNat_zero] at this
  have sV : ∀ {a n : Nat}, a + n ≤ oTop → Region.Sub ⟨σ.gpr .r8 + BitVec.ofNat 64 a, n⟩ ⟨σ.gpr .r8, oTop⟩ :=
    fun ha => Offset.sub_base _ ha
  have sC : Region.Sub (cR (σ.gpr .r8)) ⟨σ.gpr .r8, oTop⟩ := Region.sub_prefix (by decide)
  have sS : ∀ {r : Region}, Region.Sub r ⟨σ.gpr .r8, oTop⟩ → Region.Sub r ⟨σ.gpr .r8, kScrE⟩ :=
    fun hr x hx => sub_topG x (hr x hx)
  have bU : oQ (2 * L.k) + 1024 * L.k ≤ oTop := by simp only [oQ, oTop]; omega_using [hk4]
  have cE : Covers [⟨σ.gpr .rcx + BitVec.ofNat 64 (512 * L.k), 512 * L.k⟩] (s.rd ++ s.wr) :=
    covers_one (inR E hkt (by omega) (by rcases W.k34 with e | e <;> rw [e] <;> decide))
  have bS : oQ 0 + 1024 * L.k ≤ oTop := by simp only [oQ, oTop]; omega_using [hk4]
  have cA : Covers [⟨σ.gpr .rdx, 512 * (L.k * L.k)⟩] (s.rd ++ s.wr) := by
    have := covers_one (inA E hkt (o := 0) (n := 512 * (L.k * L.k)) (by omega) hkk)
    rwa [add_ofNat_zero] at this
  have cZ : ∀ {X : List Region}, (∀ {o n : Nat}, o + n ≤ kScrE → InRegions X (σ.gpr .r8 + BitVec.ofNat 64 o) n) →
      Covers [cR (σ.gpr .r8)] X := fun hX => by
    have := covers_one (hX (o := 0) (n := 4096) (by decide))
    rwa [add_ofNat_zero] at this
  refine WP.mono (glueIn_ok hv hn (emGlue_ok (qP (2 * L.k)) (qP 0) (.r12, 0) (.r13, 512 * L.k) (.rbx, 0)
      ⟨by simp only [oQ]; omega_using [hk4], by simp only [oQ]; omega_using [hk4], by decide,
        by omega, by decide⟩
      (na_rbx _) (by simp [NA, argRegs]) (by simp [NA, argRegs]) (na_rbx _) s)
    (rd := [⟨σ.gpr .rdx, 512 * (L.k * L.k)⟩, ⟨σ.gpr .rcx + BitVec.ofNat 64 (512 * L.k), 512 * L.k⟩])
    (wr := [vR (σ.gpr .r8 + BitVec.ofNat 64 (oQ (2 * L.k))) L.k, vR (σ.gpr .r8 + BitVec.ofNat 64 (oQ 0)) L.k,
      cR (σ.gpr .r8)])
    (fun s1 hV hm k1 => ?_) ?_ ?_) fun s' ⟨hP, s1, hV, hm, k1, hq⟩ => ?_
  · simp only [kgMulK16, kgMulKG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_mem, hV.1, hV.2.1, hV.2.2.1, hV.2.2.2.1, hV.2.2.2.2, hm, eU, eE, eS, eA, eZ]
    have rS := fun {R : Region} (hR : Region.Sub R ⟨σ.gpr .r8, kScrE⟩) =>
      retR_keep k1 (by rw [retR_eq hkt]; exact E.xX.sub_right hR) [⟨σ.gpr .rdx, 512 * (L.k * L.k)⟩,
        ⟨σ.gpr .rcx + BitVec.ofNat 64 (512 * L.k), 512 * L.k⟩]
        [vR (σ.gpr .r8 + BitVec.ofNat 64 (oQ (2 * L.k))) L.k, vR (σ.gpr .r8 + BitVec.ofNat 64 (oQ 0)) L.k,
          cR (σ.gpr .r8)]
    refine ⟨trivial, trivial,
      od (by simp only [oQ]; omega_using [hk4]) (by simp only [oQ, kScrE]; omega_using [hk4])
        (by simp only [oQ, kScrE]; omega_using [hk4]),
      E.aX.symm.sub_left (sS (sV bU)),
      (E.sX.symm.sub_left (sS (sV bU))).sub_right sE,
      od0 (by simp only [oQ]; omega_using [hk4]) (by simp only [oQ, kScrE]; omega_using [hk4]),
      E.aX.symm.sub_left (sS (sV bS)),
      (E.sX.symm.sub_left (sS (sV bS))).sub_right sE,
      od0 (by simp only [oQ]; omega_using [hk4]) (by simp only [oQ, kScrE]; omega_using [hk4]),
      E.aX.sub_right (sS sC),
      (E.sX.sub_left sE).sub_right (sS sC),
      rS (sS (sV bU)), rS (sS (sV bS)), retR_keep k1 (by rw [retR_eq hkt]; exact E.xA) _ _,
      retR_keep k1 (by rw [retR_eq hkt]; exact E.xS.sub_right sE) _ _,
      rS (sS sC), fun i hi => ?_, fun e he => ?_, fun i hi => ?_⟩
    · rw [q_add, Nat.zero_add]; exact (h.y i (by omega)).1
    · rw [show 32 * 16 * e = 512 * e by omega]; exact (hkt.aW E he).1
    · rw [off_add, show 512 * L.k + 32 * 16 * i = 512 * (L.k + i) by omega]; exact (hkt.rW E (by omega)).1
  · exact covers_append (covers_cons cA (covers_cons cE covers_nil))
      (covers_cons (covers_one (inS' E hkt (by simp only [oQ, kScrE]; omega)))
        (covers_cons (covers_one (inS' E hkt (by simp only [oQ, kScrE]; omega))) (covers_cons (cZ (inS' E hkt))
        covers_nil)))
  · exact covers_cons (covers_one (inS E hkt (by simp only [oQ, kScrE]; omega)))
      (covers_cons (covers_one (inS E hkt (by simp only [oQ, kScrE]; omega))) (covers_cons (cZ (inS E hkt))
      covers_nil))
  simp only [kgMulK16, kgMulKG, State.withRegions_gpr, State.withRegions_mem, hV.1, hV.2.1, hV.2.2.1,
    hV.2.2.2.1, hm, eU, eE, eS, eA] at hq
  have hs : (vecAt s.mem (σ.gpr .r8 + BitVec.ofNat 64 (oQ 0)) L.k).map ntt = sHat L σ := by
    simp only [vecAt, sHat, vecAtW, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    simp only [Function.comp_apply]
    rw [q_add, Nat.zero_add, (h.y j (by have := List.mem_range.mp hj; omega)).2, KpkeEnc.rW,
      show 32 * 16 * j = 512 * j by omega]
  have he : (vecAtW 16 s.mem (σ.gpr .rcx + BitVec.ofNat 64 (512 * L.k)) L.k).map ntt = eHat L σ := by
    simp only [eHat, vecAtW, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    simp only [Function.comp_apply]
    rw [off_add, show 512 * L.k + 32 * 16 * j = 512 * (L.k + j) by omega,
      (hkt.rW E (by have := List.mem_range.mp hj; omega)).2, KpkeEnc.rW]
  rw [hs, he, hkt.mat E] at hq
  refine ⟨hkt.step E hP fun r hr => ?_, fun i hi _ => ?_, fun j hj _ => ?_, fun i hi => absurd hi (Nat.not_lt_zero _),
    fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [.inl (sV bU), .inl (sV bS), .inl sC]
  · rw [← q_add]; exact hq.2.2 i hi
  · have := hq.1.2 j hj; rwa [q_add, Nat.zero_add] at this

/-! ## `ek` and `dk` -/

omit E in
theorem pa_r15 {s : State} (h : KT L σ s) (o : Nat) : pa s (.r15, o) = σ.gpr .rdi + BitVec.ofNat 64 o := by
  simp only [pa, h.r15]

omit E in
theorem pa_rbp {s : State} (h : KT L σ s) (o : Nat) : pa s (.rbp, o) = σ.gpr .rsi + BitVec.ofNat 64 o := by
  simp only [pa, h.rbp]

theorem ek_ok {A : Arith} (hA : ArithOk A) (W : KpkeEnc.KeWf L) (hn : A.enc12.noCalls = true) {i : Nat}
    (hi : i < L.k) {s : State} (h : EO L σ i 0 s) : WP isa (ekOut L A i) s (EO L σ (i + 1) 0) := by
  have hkt := h.kt
  have hk4 : L.k ≤ 4 := by rcases W.k34 with e | e <;> omega
  have bnd : 384 * i + 384 ≤ 384 * L.k := by omega
  have e1 := pa_q hkt (2 * L.k + i)
  have e2 := pa_r15 hkt (384 * i)
  have hT := h.t i hi (Nat.le_refl _)
  have H : TwoHi (qP (2 * L.k + i)) (.r15, 384 * i) 1024 384 s :=
    { off := ⟨by simp only [oQ]; omega, by omega⟩
      d := by rw [e1, e2]; exact (E.cX.symm.sub_left (qScr (by omega))).sub_right (Offset.sub_base _ bnd)
      rP := by rw [retR_eq hkt, e1]; exact E.xX.sub_right (qScr (by omega))
      rQ := by rw [retR_eq hkt, e2]; exact E.xC.sub_right (Offset.sub_base _ bnd)
      c := by
        rw [e1, e2]
        exact covers_append (covers_one (inS' E hkt (by simp only [oQ, kScrE]; omega)))
          (covers_one (by obtain ⟨r, hr, hc⟩ := inEk E hkt bnd (by omega); exact ⟨r, List.mem_append_right _ hr, hc⟩))
      w := by rw [e2]; exact covers_one (inEk E hkt bnd (by omega)) }
  refine WP.mono (enc12In_ok hA.enc12.ok hn (by simp [NA, argRegs]) H (by rw [e1]; exact hT.1)) fun s' ⟨hP, hq⟩ => ?_
  rw [e2] at hP hq
  rw [e1, hT.2] at hq
  have dW : ∀ {p : Addr} {n : Nat}, Region.Disjoint ⟨p, n⟩ ⟨σ.gpr .rdi + BitVec.ofNat 64 (384 * i), 384⟩ →
      ∀ r ∈ [(⟨σ.gpr .rdi + BitVec.ofNat 64 (384 * i), 384⟩ : Region)], Region.Disjoint ⟨p, n⟩ r :=
    fun h r hr => by rw [List.mem_singleton] at hr; subst hr; exact h
  refine ⟨hkt.step E hP fun r hr => ?_, fun i' hi' h' => polyIs_frame hP.frame (dW ?_) (h.t i' hi' (by omega)),
    fun j hj _ => polyIs_frame hP.frame (dW ?_) (h.sh j hj (Nat.zero_le _)), fun i' hi' => ?_,
    fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  · rw [List.mem_singleton] at hr; subst hr; exact .inr (.inl (Offset.sub_base _ bnd))
  · exact (E.cX.symm.sub_left (qScr (by omega))).sub_right (Offset.sub_base _ bnd)
  · exact (E.cX.symm.sub_left (qScr (by omega))).sub_right (Offset.sub_base _ bnd)
  · rcases (by omega : i' < i ∨ i' = i) with hi'' | rfl
    · rw [bytesAt_frame hP.frame (dW (Offset.disjoint _ (.inl (by omega)) (by omega) (by omega))) (by omega)]
      exact h.ek i' hi''
    · exact hq

theorem dk_ok {A : Arith} (hA : ArithOk A) (W : KpkeEnc.KeWf L) (hn : A.enc12.noCalls = true) {j : Nat}
    (hj : j < L.k) {s : State} (h : EO L σ L.k j s) : WP isa (dkOut A j) s (EO L σ L.k (j + 1)) := by
  have hkt := h.kt
  have hk4 : L.k ≤ 4 := by rcases W.k34 with e | e <;> omega
  have bnd : 384 * j + 384 ≤ 384 * L.k := by omega
  have e1 := pa_q hkt j
  have e2 := pa_rbp hkt (384 * j)
  have hS := h.sh j hj (Nat.le_refl _)
  have H : TwoHi (qP j) (.rbp, 384 * j) 1024 384 s :=
    { off := ⟨by simp only [oQ]; omega, by omega⟩
      d := by rw [e1, e2]; exact (E.dX.symm.sub_left (qScr (by omega))).sub_right (Offset.sub_base _ bnd)
      rP := by rw [retR_eq hkt, e1]; exact E.xX.sub_right (qScr (by omega))
      rQ := by rw [retR_eq hkt, e2]; exact E.xD.sub_right (Offset.sub_base _ bnd)
      c := by
        rw [e1, e2]
        exact covers_append (covers_one (inS' E hkt (by simp only [oQ, kScrE]; omega)))
          (covers_one (by obtain ⟨r, hr, hc⟩ := inDk E hkt bnd (by omega); exact ⟨r, List.mem_append_right _ hr, hc⟩))
      w := by rw [e2]; exact covers_one (inDk E hkt bnd (by omega)) }
  refine WP.mono (enc12In_ok hA.enc12.ok hn (by simp [NA, argRegs]) H (by rw [e1]; exact hS.1)) fun s' ⟨hP, hq⟩ => ?_
  rw [e2] at hP hq
  rw [e1, hS.2] at hq
  have dW : ∀ {p : Addr} {n : Nat}, Region.Disjoint ⟨p, n⟩ ⟨σ.gpr .rsi + BitVec.ofNat 64 (384 * j), 384⟩ →
      ∀ r ∈ [(⟨σ.gpr .rsi + BitVec.ofNat 64 (384 * j), 384⟩ : Region)], Region.Disjoint ⟨p, n⟩ r :=
    fun h r hr => by rw [List.mem_singleton] at hr; subst hr; exact h
  have bEk : ∀ i < L.k, 384 * i + 384 ≤ 384 * L.k := fun i hi => by omega
  refine ⟨hkt.step E hP fun r hr => ?_, fun i hi h' => absurd h' (by omega),
    fun j' hj' h' => polyIs_frame hP.frame (dW ?_) (h.sh j' hj' (by omega)), fun i hi => ?_, fun j' hj' => ?_⟩
  · rw [List.mem_singleton] at hr; subst hr; exact .inr (.inr (Offset.sub_base _ bnd))
  · exact (E.dX.symm.sub_left (qScr (by omega))).sub_right (Offset.sub_base _ bnd)
  · rw [bytesAt_frame hP.frame (dW ((E.cD.sub_left (Offset.sub_base _ (bEk i hi))).sub_right
      (Offset.sub_base _ bnd))) (by omega)]
    exact h.ek i hi
  · rcases (by omega : j' < j ∨ j' = j) with hj'' | rfl
    · rw [bytesAt_frame hP.frame (dW (Offset.disjoint _ (.inl (by omega)) (by omega) (by omega))) (by omega)]
      exact h.dk j' hj''
    · exact hq

omit E in
/-- `encodeVec` of `k` polynomials, from the encodings of each. -/
theorem enc_eq {m : Mem} {p : Addr} {v : List Poly} (hv : v.length = L.k)
    (h : ∀ i < L.k, bytesAt m (p + BitVec.ofNat 64 (384 * i)) 384 = encode12 (v.getD i zero)) :
    bytesAt m p (384 * L.k) = encodeVec v := by
  have e : v = (List.range L.k).map fun i => v.getD i zero := list_eq_map_getD hv
  rw [bytesAt_cat m p 384 _ L.k h, encodeVec]
  calc _ = ((List.range L.k).map fun i => v.getD i zero).flatMap encode12 := by rw [List.flatMap_map]
    _ = v.flatMap encode12 := by rw [← e]

end

/-! ## The function -/

/-- The prologue, `s`, `e` and the products. -/
theorem pre_wp {L : Kem} (W : KpkeEnc.KeWf L) {mul : Nat → Prog isa}
    (hv : ∀ s, (kgMulK16 L.k).pre s → ∃ t s', Exec isa (mul L.k) s t s' ∧ abiPreserved s s' ∧
      (kgMulK16 L.k).post s s')
    (hn : (mul L.k).noCalls = true) {σ : State} (hp : (kpkeKgK L).pre σ) :
    WP isa (kpkeKgPre L mul) σ (EO L σ 0 0) := by
  have E := ep hp
  refine WP.seq (WP.mono (pro_ok E) fun s₁ h₁ => ?_)
  have d₀ : ER L σ 0 s₁ := ⟨h₁, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  refine WP.seq (WP.mono (seqR_ok (I := fun j s => ER L σ j s) L.k 0
    (fun j _ hj s h => y_ok E W (by omega) h) s₁ d₀) fun s₂ h₂ => ?_)
  rw [Nat.zero_add] at h₂
  exact mul_ok E W hv hn h₂

/-- `ek`, `dk` and the epilogue. -/
theorem post_wp {L : Kem} {A : Arith} (hA : ArithOk A) (W : KpkeEnc.KeWf L) (hn : A.enc12.noCalls = true)
    {σ : State} (hp : (kpkeKgK L).pre σ) {s : State} (h : EO L σ 0 0 s) :
    WP isa (kpkeKgPost L A) s fun s' => gprPreserved σ s' ∧ (kpkeKgK L).post σ s' := by
  have E := ep hp
  have hk4 : L.k ≤ 4 := by rcases W.k34 with e | e <;> omega
  refine WP.seq (WP.mono (seqR_ok (I := fun i s => EO L σ i 0 s) L.k 0
    (fun i _ hi s h => ek_ok E hA W hn (by omega) h) s h) fun s₁ h₁ => ?_)
  rw [Nat.zero_add] at h₁
  refine WP.seq (WP.mono (seqR_ok (I := fun j s => EO L σ L.k j s) L.k 0
    (fun j _ hj s h => dk_ok E hA W hn (by omega) h) s₁ h₁) fun s₂ h₂ => ?_)
  rw [Nat.zero_add] at h₂
  refine WP.mono (epi_ok E h₂.kt) fun s₃ ⟨hg, hm⟩ => ⟨hg, ?_, ?_⟩
  · show bytesAt _ _ _ = _
    rw [hm]
    exact enc_eq (by simp [addVec, mulMatVec, matAtW, vecAtW]) h₂.ek
  · show bytesAt _ _ _ = _
    rw [hm]
    exact enc_eq (by simp [vecAtW]) h₂.dk

theorem kpkeKg_wp {L : Kem} {A : Arith} (hA : ArithOk A) (W : KpkeEnc.KeWf L) {mul : Nat → Prog isa}
    (hv : ∀ s, (kgMulK16 L.k).pre s → ∃ t s', Exec isa (mul L.k) s t s' ∧ abiPreserved s s' ∧
      (kgMulK16 L.k).post s s')
    (hn : (mul L.k).noCalls = true) (hnE : A.enc12.noCalls = true) {σ : State} (hp : (kpkeKgK L).pre σ) :
    WP isa (kpkeKg L A mul) σ fun s' => gprPreserved σ s' ∧ (kpkeKgK L).post σ s' :=
  WP.seq (WP.mono (pre_wp W hv hn hp) fun _ h => post_wp hA W hnE hp h)

theorem kpkeKg_correct {L : Kem} {A : Arith} (hA : ArithOk A) (W : KpkeEnc.KeWf L) {mul : Nat → Prog isa}
    (hv : ∀ s, (kgMulK16 L.k).pre s → ∃ t s', Exec isa (mul L.k) s t s' ∧ abiPreserved s s' ∧
      (kgMulK16 L.k).post s s')
    (hn : (mul L.k).noCalls = true) (hnE : A.enc12.noCalls = true) (hctl : ctlOk (kpkeKg L A mul) = true)
    (σ : State) (hp : (kpkeKgK L).pre σ) :
    ∃ t s', Exec isa (kpkeKg L A mul) σ t s' ∧ abiPreserved σ s' ∧ (kpkeKgK L).post σ s' := by
  obtain ⟨t, s', he, hg, hq⟩ := kpkeKg_wp hA W hv hn hnE hp
  exact ⟨t, s', he, abiPreserved_of_ctl hctl he hg, hq⟩

end KpkeKg

end VG.Proof.MlKem.X86_64

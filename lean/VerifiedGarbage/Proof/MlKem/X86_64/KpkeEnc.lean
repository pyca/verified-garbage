module

public import VerifiedGarbage.Proof.MlKem.X86_64.KpkeDec
public import VerifiedGarbage.Proof.MlKem.X86_64.Widen
public import VerifiedGarbage.Proof.MlKem.X86_64.EncMul
public import VerifiedGarbage.Proof.MlKem.X86_64.FragEM
public import VerifiedGarbage.Proof.MlKem.X86_64.Add16
import VerifiedGarbage.Proof.MlKem.X86_64.FragPrim
import VerifiedGarbage.Proof.MlKem.X86_64.DcDec

/-!
# ML-KEM on x86-64: `vg_mlkem*_kpke_encrypt`

The contract (`kpkeEncK`), what holds throughout the function (`KT`: the
pointers, the saved registers, and that only `scratch` and `ct` change),
and the steps: the prologue, each polynomial primitive inline (`KT.step`
keeps `KT` across one that writes only below the saved registers or to
`ct`), the product (the code of `vg_mlkem*_encrypt_mul` reading `Â` as
`u16`s, inline), and the epilogue. `y` becomes `u32`s with `vunpack`
(`widenIn_ok`); `e₁` and `e₂` are added as `u16`s (`add16In_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- The size of `vg_mlkem*_kpke_encrypt`'s `scratch`. -/
abbrev kScrE : Nat := 20480

/-- The ciphertext of `K-PKE.Encrypt` of the inputs in `m`, as
`Params.kpkeEncryptContract` states it. -/
def encCt (L : Kem) (m : Mem) (a t r msg : Addr) : List Byte :=
  let tHat := decodeVec L.k (bytesAt m t (384 * L.k))
  let ŷ := (vecAtW 16 m r L.k).map ntt
  let e₁ := vecAtW 16 m (r + BitVec.ofNat 64 (512 * L.k)) L.k
  let e₂ := polyAtW 16 m (r + BitVec.ofNat 64 (1024 * L.k))
  let u := addVec ((mulMatTVec L.k (matAtW 16 m a L.k) ŷ).map nttInv) e₁
  let μ := decodeDecompress 1 (bytesAt m msg 32)
  let v := add (add (nttInv (dot tHat ŷ)) e₂) μ
  u.flatMap (compressEncode L.du) ++ compressEncode L.dv v

/-- `vg_mlkem*_kpke_encrypt(ct = rdi, a = rsi, t = rdx, r = rcx, m = r8, scratch = r9)` of the
parameter set `L`. -/
def kpkeEncK (L : Kem) : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rsi, 512 * (L.k * L.k)⟩, ⟨s.gpr .rdx, 384 * L.k⟩, ⟨s.gpr .r8, 32⟩] ∧
    s.wr = [⟨s.gpr .rdi, L.ctLen⟩, ⟨s.gpr .rcx, 512 * (2 * L.k + 1)⟩, ⟨s.gpr .r9, kScrE⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, L.ctLen⟩ ⟨s.gpr .rsi, 512 * (L.k * L.k)⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, L.ctLen⟩ ⟨s.gpr .rdx, 384 * L.k⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, L.ctLen⟩ ⟨s.gpr .rcx, 512 * (2 * L.k + 1)⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, L.ctLen⟩ ⟨s.gpr .r8, 32⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, L.ctLen⟩ ⟨s.gpr .r9, kScrE⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, 512 * (L.k * L.k)⟩ ⟨s.gpr .rcx, 512 * (2 * L.k + 1)⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, 512 * (L.k * L.k)⟩ ⟨s.gpr .r9, kScrE⟩ ∧
    Region.Disjoint ⟨s.gpr .rdx, 384 * L.k⟩ ⟨s.gpr .rcx, 512 * (2 * L.k + 1)⟩ ∧
    Region.Disjoint ⟨s.gpr .rdx, 384 * L.k⟩ ⟨s.gpr .r9, kScrE⟩ ∧
    Region.Disjoint ⟨s.gpr .rcx, 512 * (2 * L.k + 1)⟩ ⟨s.gpr .r8, 32⟩ ∧
    Region.Disjoint ⟨s.gpr .rcx, 512 * (2 * L.k + 1)⟩ ⟨s.gpr .r9, kScrE⟩ ∧
    Region.Disjoint ⟨s.gpr .r8, 32⟩ ⟨s.gpr .r9, kScrE⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, L.ctLen⟩ ∧ (retR s).Disjoint ⟨s.gpr .rsi, 512 * (L.k * L.k)⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdx, 384 * L.k⟩ ∧ (retR s).Disjoint ⟨s.gpr .rcx, 512 * (2 * L.k + 1)⟩ ∧
    (retR s).Disjoint ⟨s.gpr .r8, 32⟩ ∧ (retR s).Disjoint ⟨s.gpr .r9, kScrE⟩ ∧
    (s.gpr .rdi).toNat + L.ctLen ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 512 * (L.k * L.k) ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + 384 * L.k ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 512 * (2 * L.k + 1) ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + kScrE ≤ 2 ^ 64 ∧
    VecReducedW 16 s.mem (s.gpr .rsi) (L.k * L.k) ∧ VecReducedW 16 s.mem (s.gpr .rcx) (2 * L.k + 1)
  post s s' := bytesAt s'.mem (s.gpr .rdi) L.ctLen =
    encCt L s.mem (s.gpr .rsi) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r8)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-! ## `vunpack` inline -/

theorem widenGlue_ok (b f : Ptr) (hb : b.2 < 2 ^ 31) (hf : f.2 < 2 ^ 31) (hfr : f.1 ≠ .rdx) (s : State) :
    WP isa (.block (lea .rdx b ++ lea .r9 f)) s fun s1 =>
      ((s1.gpr .rdx = pa s b ∧ s1.gpr .r9 = pa s f) ∧ s1.mem = s.mem) ∧ Keep argRegs s s1 := by
  refine WP.keep _ ?_ (by rfl)
  unfold lea
  xrun [sx_ofNat hb, sx_ofNat hf, hfr, List.cons_append, List.nil_append]

theorem vunpack_cs : ∀ r ∈ calleeSaved, ∀ i ∈ instrs vunpack, X86_64.Taint.clobbers i r = false := by
  decide

/-- `widenIn b f`: the polynomial of `u16`s at `b` as `u32`s at `f`. -/
theorem widenIn_ok {b f : Ptr} (hb : b.2 < 2 ^ 31) (hf : f.2 < 2 ^ 31) (hfr : f.1 ≠ .rdx) {s : State} {F : Poly}
    (hS : PolyIsW 16 s.mem (pa s b) F) (hd : (pR (pa s f)).Disjoint ⟨pa s b, 512⟩)
    (hc : Covers ([⟨pa s b, 512⟩] ++ [pR (pa s f)]) (s.rd ++ s.wr)) (hw : Covers [pR (pa s f)] s.wr) :
    WP isa (Kpke16.widenIn b f) s fun s' => IPost s s' [pR (pa s f)] ∧ PolyIs s'.mem (pa s f) F := by
  unfold Kpke16.widenIn
  refine WP.seq (WP.mono (widenGlue_ok b f hb hf hfr s) fun s1 ⟨⟨⟨h1dx, h19⟩, hm1⟩, k1⟩ => ?_)
  refine WP.narrowIn (rd := [⟨pa s b, 512⟩]) (wr := [pR (pa s f)])
    (widen_ok (s := s1.withRegions [⟨pa s b, 512⟩] [pR (pa s f)]) (dP := pa s f) (src := pa s b) (F := F)
      (by simp only [State.withRegions_mem, hm1]; exact hS) (by simp only [State.withRegions_gpr, h19])
      (by simp only [State.withRegions_gpr, h1dx]) (by simp only [State.withRegions_wr]; exact List.mem_singleton_self _)
      (by simp only [State.withRegions_rd, State.withRegions_wr]
          exact ⟨_, List.mem_cons_self .., Region.contains_self _ _⟩) hd)
    (by rw [k1.2.1, k1.2.2]; exact hc) (by rw [k1.2.2]; exact hw) (by decide) fun s' hrd hwr hfr' hg ⟨hP, _⟩ => ?_
  refine ⟨⟨hrd.trans k1.2.1, hwr.trans k1.2.2, fun r hr => by
      rw [hg r (vunpack_cs r hr), k1.gpr (argRegs_cs r hr)], by rw [hm1] at hfr'; exact hfr'⟩, ?_⟩
  simpa only [State.withRegions_mem] using hP

namespace KpkeEnc

open VG.Impl.MlKem.X86_64.Kpke16

/-- The polynomials and the working space lie below this offset of `scratch`. -/
abbrev oTop : Nat := 19456

/-- The facts of the precondition, by name. -/
structure EP (L : Kem) (σ : State) : Prop where
  rd : σ.rd = [⟨σ.gpr .rsi, 512 * (L.k * L.k)⟩, ⟨σ.gpr .rdx, 384 * L.k⟩, ⟨σ.gpr .r8, 32⟩]
  wr : σ.wr = [⟨σ.gpr .rdi, L.ctLen⟩, ⟨σ.gpr .rcx, 512 * (2 * L.k + 1)⟩, ⟨σ.gpr .r9, kScrE⟩]
  cA : Region.Disjoint ⟨σ.gpr .rdi, L.ctLen⟩ ⟨σ.gpr .rsi, 512 * (L.k * L.k)⟩
  cT : Region.Disjoint ⟨σ.gpr .rdi, L.ctLen⟩ ⟨σ.gpr .rdx, 384 * L.k⟩
  cR : Region.Disjoint ⟨σ.gpr .rdi, L.ctLen⟩ ⟨σ.gpr .rcx, 512 * (2 * L.k + 1)⟩
  cM : Region.Disjoint ⟨σ.gpr .rdi, L.ctLen⟩ ⟨σ.gpr .r8, 32⟩
  cS : Region.Disjoint ⟨σ.gpr .rdi, L.ctLen⟩ ⟨σ.gpr .r9, kScrE⟩
  aR : Region.Disjoint ⟨σ.gpr .rsi, 512 * (L.k * L.k)⟩ ⟨σ.gpr .rcx, 512 * (2 * L.k + 1)⟩
  aS : Region.Disjoint ⟨σ.gpr .rsi, 512 * (L.k * L.k)⟩ ⟨σ.gpr .r9, kScrE⟩
  tR : Region.Disjoint ⟨σ.gpr .rdx, 384 * L.k⟩ ⟨σ.gpr .rcx, 512 * (2 * L.k + 1)⟩
  tS : Region.Disjoint ⟨σ.gpr .rdx, 384 * L.k⟩ ⟨σ.gpr .r9, kScrE⟩
  rM : Region.Disjoint ⟨σ.gpr .rcx, 512 * (2 * L.k + 1)⟩ ⟨σ.gpr .r8, 32⟩
  rS : Region.Disjoint ⟨σ.gpr .rcx, 512 * (2 * L.k + 1)⟩ ⟨σ.gpr .r9, kScrE⟩
  mS : Region.Disjoint ⟨σ.gpr .r8, 32⟩ ⟨σ.gpr .r9, kScrE⟩
  xC : (retR σ).Disjoint ⟨σ.gpr .rdi, L.ctLen⟩
  xA : (retR σ).Disjoint ⟨σ.gpr .rsi, 512 * (L.k * L.k)⟩
  xT : (retR σ).Disjoint ⟨σ.gpr .rdx, 384 * L.k⟩
  xR : (retR σ).Disjoint ⟨σ.gpr .rcx, 512 * (2 * L.k + 1)⟩
  xM : (retR σ).Disjoint ⟨σ.gpr .r8, 32⟩
  xS : (retR σ).Disjoint ⟨σ.gpr .r9, kScrE⟩
  nC : (σ.gpr .rdi).toNat + L.ctLen ≤ 2 ^ 64
  nA : (σ.gpr .rsi).toNat + 512 * (L.k * L.k) ≤ 2 ^ 64
  nT : (σ.gpr .rdx).toNat + 384 * L.k ≤ 2 ^ 64
  nR : (σ.gpr .rcx).toNat + 512 * (2 * L.k + 1) ≤ 2 ^ 64
  nM : (σ.gpr .r8).toNat + 32 ≤ 2 ^ 64
  nS : (σ.gpr .r9).toNat + kScrE ≤ 2 ^ 64
  redA : VecReducedW 16 σ.mem (σ.gpr .rsi) (L.k * L.k)
  redR : VecReducedW 16 σ.mem (σ.gpr .rcx) (2 * L.k + 1)

theorem ep {L : Kem} {σ : State} (hp : (kpkeEncK L).pre σ) : EP L σ :=
  let ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
    h23, h24, h25, h26, h27⟩ := hp
  ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23,
    h24, h25, h26, h27⟩

/-- The regions of `σ` that the function may change. -/
abbrev chg (L : Kem) (σ : State) : List Region := [⟨σ.gpr .r9, kScrE⟩, ⟨σ.gpr .rdi, L.ctLen⟩]

/-- What holds throughout the function entered in `σ`. -/
structure KT (L : Kem) (σ s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  rsp : s.gpr .rsp = σ.gpr .rsp
  rbx : s.gpr .rbx = σ.gpr .r9
  rbp : s.gpr .rbp = σ.gpr .rsi
  r12 : s.gpr .r12 = σ.gpr .rdx
  r13 : s.gpr .r13 = σ.gpr .rcx
  r14 : s.gpr .r14 = σ.gpr .r8
  r15 : s.gpr .r15 = σ.gpr .rdi
  saved : ∀ i < 6, s.mem.readW (σ.gpr .r9 + BitVec.ofNat 64 (oKSE + 8 * i)) 64 = σ.gpr (kRegs.getD i .rbx)
  ret : s.mem.readW (σ.gpr .rsp) 64 = σ.mem.readW (σ.gpr .rsp) 64
  fr : Frame (chg L σ) σ.mem s.mem

section
variable {L : Kem} {σ : State} (E : EP L σ)
include E

omit E in
theorem sub_top : Region.Sub ⟨σ.gpr .r9, oTop⟩ ⟨σ.gpr .r9, kScrE⟩ := Region.sub_prefix (by decide)

/-- A region the steps write: below `oTop` in `scratch`, or in `ct`. -/
abbrev WOk (L : Kem) (σ : State) (r : Region) : Prop :=
  Region.Sub r ⟨σ.gpr .r9, oTop⟩ ∨ Region.Sub r ⟨σ.gpr .rdi, L.ctLen⟩

/-- A region the steps write is apart from the saved registers and the return address. -/
theorem wok_disj {r : Region} (hr : WOk L σ r) :
    (retR σ).Disjoint r ∧ ∀ i < 6, Region.Disjoint ⟨σ.gpr .r9 + BitVec.ofNat 64 (oKSE + 8 * i), 8⟩ r := by
  rcases hr with hr | hr
  · refine ⟨(E.xS.sub_right sub_top).sub_right hr, fun i hi => ?_⟩
    exact (Offset.disjoint_base (σ.gpr .r9) (d := oKSE + 8 * i) (n := 8) (k := oTop)
      (by simp only [oKSE, oTop]; omega) (by have := E.nS; simp only [oKSE, kScrE] at *; omega)).sub_right hr
  · refine ⟨E.xC.sub_right hr, fun i hi => ?_⟩
    have hs : Region.Sub ⟨σ.gpr .r9 + BitVec.ofNat 64 (oKSE + 8 * i), 8⟩ ⟨σ.gpr .r9, kScrE⟩ :=
      Offset.sub_base _ (by simp only [oKSE, kScrE]; omega)
    exact ((E.cS.symm.sub_left hs).sub_right hr)

omit E in
theorem wok_chg {r : Region} (hr : WOk L σ r) : ∃ r' ∈ chg L σ, Region.Sub r r' := by
  rcases hr with hr | hr
  · exact ⟨_, List.mem_cons_self .., fun x hx => sub_top x (hr x hx)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), hr⟩

theorem KT.stepF {s s' : State} (h : KT L σ s) {W : List Region} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.gpr .rsp = s.gpr .rsp) (hcs : ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15], s'.gpr r = s.gpr r)
    (hf : Frame W s.mem s'.mem) (hW : ∀ r ∈ W, WOk L σ r) : KT L σ s' := by
  have D := fun r hr => wok_disj E (r := r) (hW r hr)
  refine ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.rsp, (hcs .rbx (by simp)).trans h.rbx,
    (hcs .rbp (by simp)).trans h.rbp, (hcs .r12 (by simp)).trans h.r12, (hcs .r13 (by simp)).trans h.r13,
    (hcs .r14 (by simp)).trans h.r14, (hcs .r15 (by simp)).trans h.r15, fun i hi => ?_, ?_,
    h.fr.trans (hf.sub fun r hr => wok_chg (hW r hr))⟩
  · rw [hf.readW (Region.contains_self _ _) (fun r hr => (D r hr).2 i hi) (by decide)]
    exact h.saved i hi
  · rw [hf.readW (Region.contains_self _ _) (fun r hr => (D r hr).1) (by decide)]
    exact h.ret

theorem KT.step {s s' : State} (h : KT L σ s) {W : List Region} (hP : IPost s s' W)
    (hW : ∀ r ∈ W, WOk L σ r) : KT L σ s' :=
  h.stepF E hP.rd hP.wr hP.rsp (fun r hr => hP.cs r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) hP.frame hW

/-! ## Inputs -/

omit E in
/-- Bytes apart from `scratch` and `ct` are as on entry. -/
theorem KT.bytes {s : State} (h : KT L σ s) {p : Addr} {n : Nat} (hd : ∀ r ∈ chg L σ, Region.Disjoint ⟨p, n⟩ r)
    (hn : n ≤ 2 ^ 64) : bytesAt s.mem p n = bytesAt σ.mem p n :=
  bytesAt_frame h.fr hd hn

theorem KT.bT {s : State} (h : KT L σ s) : bytesAt s.mem (σ.gpr .rdx) (384 * L.k) = bytesAt σ.mem (σ.gpr .rdx) (384 * L.k) :=
  h.bytes (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [E.tS, E.cT.symm]) (by have := E.nT; omega)

theorem KT.bM {s : State} (h : KT L σ s) : bytesAt s.mem (σ.gpr .r8) 32 = bytesAt σ.mem (σ.gpr .r8) 32 :=
  h.bytes (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [E.mS, E.cM.symm]) (by omega)

/-- Polynomial `i` of `r` (`u16`s), as on entry. -/
theorem KT.rW {s : State} (h : KT L σ s) {i : Nat} (hi : i < 2 * L.k + 1) :
    PolyIsW 16 s.mem (σ.gpr .rcx + BitVec.ofNat 64 (512 * i))
      (polyAtW 16 σ.mem (σ.gpr .rcx + BitVec.ofNat 64 (512 * i))) := by
  have hs : Region.Sub ⟨σ.gpr .rcx + BitVec.ofNat 64 (512 * i), 512⟩ ⟨σ.gpr .rcx, 512 * (2 * L.k + 1)⟩ :=
    Offset.sub_base _ (by omega)
  refine polyIsW16_frame h.fr (fun r hr => ?_) ⟨?_, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [E.rS.sub_left hs, E.cR.symm.sub_left hs]
  · have := E.redR i hi
    rwa [show 32 * 16 * i = 512 * i by omega] at this

/-- Polynomial `e` of `a` (`u16`s), as on entry. -/
theorem KT.aW {s : State} (h : KT L σ s) {e : Nat} (he : e < L.k * L.k) :
    PolyIsW 16 s.mem (σ.gpr .rsi + BitVec.ofNat 64 (512 * e))
      (polyAtW 16 σ.mem (σ.gpr .rsi + BitVec.ofNat 64 (512 * e))) := by
  have hs : Region.Sub ⟨σ.gpr .rsi + BitVec.ofNat 64 (512 * e), 512⟩ ⟨σ.gpr .rsi, 512 * (L.k * L.k)⟩ :=
    Offset.sub_base _ (by omega)
  refine polyIsW16_frame h.fr (fun r hr => ?_) ⟨?_, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [E.aS.sub_left hs, E.cA.symm.sub_left hs]
  · have := E.redA e he
    rwa [show 32 * 16 * e = 512 * e by omega] at this


/-! ## The prologue and the epilogue -/

omit E in
theorem proE_eq : proE = [.store (at_ .r9 19456) .rbx, .store (at_ .r9 19464) .rbp, .store (at_ .r9 19472) .r12,
    .store (at_ .r9 19480) .r13, .store (at_ .r9 19488) .r14, .store (at_ .r9 19496) .r15,
    .mov .rbx (.reg .r9), .mov .r15 (.reg .rdi), .mov .rbp (.reg .rsi), .mov .r12 (.reg .rdx),
    .mov .r13 (.reg .rcx), .mov .r14 (.reg .r8)] := rfl

omit E in
/-- The six stores of `proE`: each slot holds its register. -/
theorem stores_read (m : Mem) (a : Addr) (v : Nat → BitVec 64) : ∀ i < 6,
    ((((((m.writeW (a + BitVec.ofNat 64 19456) (v 0)).writeW (a + BitVec.ofNat 64 19464) (v 1)).writeW
      (a + BitVec.ofNat 64 19472) (v 2)).writeW (a + BitVec.ofNat 64 19480) (v 3)).writeW
      (a + BitVec.ofNat 64 19488) (v 4)).writeW (a + BitVec.ofNat 64 19496) (v 5)).readW
      (a + BitVec.ofNat 64 (oKSE + 8 * i)) 64 = v i := by
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp (disch := omega) only [oKSE, Nat.reduceMul, Nat.reduceAdd, readW_writeW_slot, Mem.readW_writeW_self64]

theorem pro_ok : WP isa (.block proE) σ (KT L σ) := by
  have hS : ⟨σ.gpr .r9, kScrE⟩ ∈ σ.wr := by rw [E.wr]; simp
  have nS := E.nS
  have c : ∀ o, o + 8 ≤ kScrE → (⟨σ.gpr .r9, kScrE⟩ : Region).Contains (σ.gpr .r9 + BitVec.ofNat 64 o) 8 :=
    fun o ho => Offset.contains_base _ ho (by omega)
  have w : ∀ o, o + 8 ≤ kScrE → InRegions σ.wr (σ.gpr .r9 + BitVec.ofNat 64 o) 8 := fun o ho => ⟨_, hS, c o ho⟩
  have w0 := w 19456 (by decide); have w1 := w 19464 (by decide); have w2 := w 19472 (by decide)
  have w3 := w 19480 (by decide); have w4 := w 19488 (by decide); have w5 := w 19496 (by decide)
  rw [proE_eq]
  refine WP.mono (WP.keep [.rbx, .r15, .rbp, .r12, .r13, .r14] (Q := fun s =>
    s.mem = (((((σ.mem.writeW (σ.gpr .r9 + BitVec.ofNat 64 19456) (σ.gpr .rbx)).writeW
      (σ.gpr .r9 + BitVec.ofNat 64 19464) (σ.gpr .rbp)).writeW (σ.gpr .r9 + BitVec.ofNat 64 19472) (σ.gpr .r12)).writeW
      (σ.gpr .r9 + BitVec.ofNat 64 19480) (σ.gpr .r13)).writeW (σ.gpr .r9 + BitVec.ofNat 64 19488) (σ.gpr .r14)).writeW
      (σ.gpr .r9 + BitVec.ofNat 64 19496) (σ.gpr .r15) ∧
    s.gpr .rbx = σ.gpr .r9 ∧ s.gpr .r15 = σ.gpr .rdi ∧ s.gpr .rbp = σ.gpr .rsi ∧ s.gpr .r12 = σ.gpr .rdx ∧
    s.gpr .r13 = σ.gpr .rcx ∧ s.gpr .r14 = σ.gpr .r8)
    (by xrun [w0, w1, w2, w3, w4, w5]) (by decide)) fun s ⟨⟨hm, hbx, h15, hbp, h12, h13, h14⟩, k⟩ => ?_
  have hf : Frame [⟨σ.gpr .r9, kScrE⟩] σ.mem s.mem := by
    rw [hm]
    exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 19456 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 19464 (by decide))).writeW (List.mem_singleton_self _) _
      (c 19472 (by decide))).writeW (List.mem_singleton_self _) _ (c 19480 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 19488 (by decide))).writeW (List.mem_singleton_self _) _ (c 19496 (by decide)))
  refine ⟨k.2.1, k.2.2, k.gpr (by decide), hbx, hbp, h12, h13, h14, h15, fun i hi => ?_, ?_,
    hf.mono (by simp)⟩
  · rw [hm]
    exact stores_read σ.mem (σ.gpr .r9) (fun i => σ.gpr (kRegs.getD i .rbx)) i hi
  · exact hf.readW (Region.contains_self _ _) (by simpa using E.xS) (by decide)

omit E in
theorem epiE_eq : epiE = [.mov .r15 (.mem (at_ .rbx 19496)), .mov .r14 (.mem (at_ .rbx 19488)),
    .mov .r13 (.mem (at_ .rbx 19480)), .mov .r12 (.mem (at_ .rbx 19472)),
    .mov .rbp (.mem (at_ .rbx 19464)), .mov .rbx (.mem (at_ .rbx 19456))] := rfl

theorem epi_ok {s : State} (h : KT L σ s) :
    WP isa (.block epiE) s fun s' => gprPreserved σ s' ∧ s'.mem = s.mem := by
  have nS := E.nS
  have hS : ⟨σ.gpr .r9, kScrE⟩ ∈ s.wr := by rw [h.wr, E.wr]; simp
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
  rw [epiE_eq]
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

theorem inS {o n : Nat} (ho : o + n ≤ kScrE) : InRegions s.wr (σ.gpr .r9 + BitVec.ofNat 64 o) n :=
  ⟨_, by rw [h.wr, E.wr]; simp, Offset.contains_base _ ho (by have := E.nS; simp only [kScrE] at *; omega)⟩

theorem inS' {o n : Nat} (ho : o + n ≤ kScrE) : InRegions (s.rd ++ s.wr) (σ.gpr .r9 + BitVec.ofNat 64 o) n := by
  obtain ⟨r, hr, hc⟩ := inS E h ho
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem inCt {o n : Nat} (ho : o + n ≤ L.ctLen) (hn : 0 < n) : InRegions s.wr (σ.gpr .rdi + BitVec.ofNat 64 o) n :=
  ⟨_, by rw [h.wr, E.wr]; simp, Offset.contains_base _ ho (by have := E.nC; omega)⟩

theorem inCt' {o n : Nat} (ho : o + n ≤ L.ctLen) (hn : 0 < n) : InRegions (s.rd ++ s.wr) (σ.gpr .rdi + BitVec.ofNat 64 o) n := by
  obtain ⟨r, hr, hc⟩ := inCt E h ho hn
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem inR {o n : Nat} (ho : o + n ≤ 512 * (2 * L.k + 1)) :
    InRegions (s.rd ++ s.wr) (σ.gpr .rcx + BitVec.ofNat 64 o) n :=
  ⟨_, List.mem_append_right _ (by rw [h.wr, E.wr]; simp), Offset.contains_base _ ho (by have := E.nR; omega)⟩

theorem inT {o n : Nat} (ho : o + n ≤ 384 * L.k) : InRegions (s.rd ++ s.wr) (σ.gpr .rdx + BitVec.ofNat 64 o) n :=
  ⟨_, List.mem_append_left _ (by rw [h.rd, E.rd]; simp), Offset.contains_base _ ho (by have := E.nT; omega)⟩

theorem inM {o n : Nat} (ho : o + n ≤ 32) : InRegions (s.rd ++ s.wr) (σ.gpr .r8 + BitVec.ofNat 64 o) n :=
  ⟨_, List.mem_append_left _ (by rw [h.rd, E.rd]; simp), Offset.contains_base _ ho (by have := E.nM; omega)⟩

theorem inA {o n : Nat} (ho : o + n ≤ 512 * (L.k * L.k)) (hn : 0 < n) :
    InRegions (s.rd ++ s.wr) (σ.gpr .rsi + BitVec.ofNat 64 o) n :=
  ⟨_, List.mem_append_left _ (by rw [h.rd, E.rd]; simp), Offset.contains_base _ ho (by have := E.nA; omega)⟩

omit E in
theorem retR_eq : retR s = retR σ := by simp only [retR, h.rsp]

omit E in
theorem pa_q (i : Nat) : pa s (qP i) = σ.gpr .r9 + BitVec.ofNat 64 (oQ i) := by simp only [pa, h.rbx]

end

omit E in
/-- A polynomial of the working space below `oTop`. -/
theorem qSub {i : Nat} (hi : i < 14) :
    Region.Sub (pR (σ.gpr .r9 + BitVec.ofNat 64 (oQ i))) ⟨σ.gpr .r9, oTop⟩ :=
  Offset.sub_base _ (by simp only [oQ, oTop]; omega)

omit E in
theorem qScr {i : Nat} (hi : i < 14) :
    Region.Sub (pR (σ.gpr .r9 + BitVec.ofNat 64 (oQ i))) ⟨σ.gpr .r9, kScrE⟩ :=
  fun x hx => sub_top x (qSub hi x hx)

theorem qDisj {i j : Nat} (hi : i < 14) (hj : j < 14) (hij : i ≠ j) :
    (pR (σ.gpr .r9 + BitVec.ofNat 64 (oQ i))).Disjoint (pR (σ.gpr .r9 + BitVec.ofNat 64 (oQ j))) :=
  Offset.disjoint _ (by simp only [oQ]; omega) (by have := E.nS; simp only [oQ, kScrE] at *; omega)
    (by have := E.nS; simp only [oQ, kScrE] at *; omega)

/-! ## `t̂` and `y` -/

/-- The bytes of `t̂`. -/
abbrev tB (L : Kem) (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdx) (384 * L.k)

/-- `y[j]`, `e₁[i]` (`j = k + i`) and `e₂` (`j = 2k`), as on entry. -/
abbrev rW (σ : State) (j : Nat) : Poly := polyAtW 16 σ.mem (σ.gpr .rcx + BitVec.ofNat 64 (512 * j))

/-- The first `nt` of `t̂` and `ny` of `y` are done. -/
structure ER (L : Kem) (σ : State) (nt ny : Nat) (s : State) : Prop where
  kt : KT L σ s
  t : ∀ i < nt, PolyIs s.mem (σ.gpr .r9 + BitVec.ofNat 64 (oQ (L.k + i))) (ekT (tB L σ) i)
  y : ∀ j < ny, PolyIs s.mem (σ.gpr .r9 + BitVec.ofNat 64 (oQ j)) (rW σ j)

/-- What the proofs need of the parameter set, decided for each. -/
structure KeWf (L : Kem) : Prop where
  k34 : L.k = 3 ∨ L.k = 4
  du : 0 < L.du ∧ L.du ≤ 11
  dv : 0 < L.dv ∧ L.dv ≤ 11
  ct : L.ctLen < 2 ^ 16

theorem ER.keep {nt ny : Nat} {s s' : State} (h : ER L σ nt ny s) {i : Nat} (hi : i < 14) (hk : L.k ≤ 4)
    (hP : IPost s s' [pR (σ.gpr .r9 + BitVec.ofNat 64 (oQ i))]) (ht : ∀ j < nt, L.k + j ≠ i)
    (hy : ∀ j < ny, j ≠ i) (hnt : nt ≤ 4) (hny : ny ≤ 4) :
    KT L σ s' ∧ (∀ j < nt, PolyIs s'.mem (σ.gpr .r9 + BitVec.ofNat 64 (oQ (L.k + j))) (ekT (tB L σ) j)) ∧
      ∀ j < ny, PolyIs s'.mem (σ.gpr .r9 + BitVec.ofNat 64 (oQ j)) (rW σ j) := by
  refine ⟨h.kt.step E hP (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact .inl (qSub hi)),
    fun j hj => polyIs_frame hP.frame ?_ (h.t j hj), fun j hj => polyIs_frame hP.frame ?_ (h.y j hj)⟩
  · intro r hr; rw [List.mem_singleton] at hr; subst hr
    exact qDisj E (by omega) hi (ht j hj)
  · intro r hr; rw [List.mem_singleton] at hr; subst hr
    exact qDisj E (by omega) hi (hy j hj)

omit E in
theorem na_rbx (o : Nat) : NA ((.rbx, o) : Ptr) := by simp [NA, argRegs]

theorem t_ok {A : Arith} (hA : ArithOk A) (W : KeWf L) (hn : A.dec12.noCalls = true) {i : Nat} (hi : i < L.k)
    {s : State} (h : ER L σ i 0 s) : WP isa (tHatE L A i) s (ER L σ (i + 1) 0) := by
  have hkt := h.kt
  have hk4 : L.k ≤ 4 := by rcases W.k34 with e | e <;> omega
  have bnd : 384 * i + 384 ≤ 384 * L.k := by omega
  have e1 : pa s ((.r12, 384 * i) : Ptr) = σ.gpr .rdx + BitVec.ofNat 64 (384 * i) := by simp only [pa, hkt.r12]
  have e2 := pa_q hkt (L.k + i)
  have H : TwoHi (.r12, 384 * i) (qP (L.k + i)) 384 1024 s :=
    { off := ⟨by omega, by simp only [oQ]; omega⟩
      d := by rw [e1, e2]; exact (E.tS.sub_left (Offset.sub_base _ bnd)).sub_right (qScr (by omega))
      rP := by rw [retR_eq hkt, e1]; exact E.xT.sub_right (Offset.sub_base _ bnd)
      rQ := by rw [retR_eq hkt, e2]; exact E.xS.sub_right (qScr (by omega))
      c := by
        rw [e1, e2]
        exact covers_append (covers_one (inT E hkt bnd)) (covers_one (inS' E hkt (by simp only [oQ, kScrE]; omega)))
      w := by rw [e2]; exact covers_one (inS E hkt (by simp only [oQ, kScrE]; omega)) }
  refine WP.mono (dec12In_ok hA.dec12.ok hn (na_rbx _) H) fun s' ⟨hP, hq⟩ => ?_
  rw [e2] at hP hq
  obtain ⟨kt', ht, -⟩ := h.keep E (i := L.k + i) (by omega) hk4 hP (fun j hj => by omega)
    (fun j hj => absurd hj (Nat.not_lt_zero _)) (by omega) (by omega)
  refine ⟨kt', fun j hj => ?_, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  rcases (by omega : j < i ∨ j = i) with hj' | rfl
  · exact ht j hj'
  · rw [e1, ← bytesAt_slice _ _ bnd, hkt.bT E] at hq
    exact hq

theorem y_ok (W : KeWf L) {j : Nat} (hj : j < L.k) {s : State} (h : ER L σ L.k j s) :
    WP isa (yE j) s (ER L σ L.k (j + 1)) := by
  have hkt := h.kt
  have hk4 : L.k ≤ 4 := by rcases W.k34 with e | e <;> omega
  have bnd : 512 * j + 512 ≤ 512 * (2 * L.k + 1) := by omega
  have e1 : pa s ((.r13, 512 * j) : Ptr) = σ.gpr .rcx + BitVec.ofNat 64 (512 * j) := by simp only [pa, hkt.r13]
  have e2 := pa_q hkt j
  refine WP.mono (widenIn_ok (b := (.r13, 512 * j)) (f := qP j) (F := rW σ j) (by omega)
    (by simp only [oQ]; omega) (by simp)
    (by rw [e1]; exact hkt.rW E (by omega))
    (by rw [e1, e2]; exact (E.rS.symm.sub_left (qScr (by omega))).sub_right (Offset.sub_base _ bnd))
    (by rw [e1, e2]
        exact covers_append (covers_one (inR E hkt bnd)) (covers_one (inS' E hkt (by simp only [oQ, kScrE]; omega))))
    (by rw [e2]; exact covers_one (inS E hkt (by simp only [oQ, kScrE]; omega)))) fun s' ⟨hP, hq⟩ => ?_
  rw [e2] at hP hq
  obtain ⟨kt', ht, hy⟩ := h.keep E (i := j) (by omega) hk4 hP (fun j' hj' => by omega)
    (fun j' hj' => by omega) (by omega) (by omega)
  refine ⟨kt', ht, fun j' hj' => ?_⟩
  rcases (by omega : j' < j ∨ j' = j) with hj'' | rfl
  · exact hy j' hj''
  · exact hq


/-! ## The products -/

/-- `ŷ`, from `y` on entry. -/
abbrev yHat (L : Kem) (σ : State) : List Poly := (vecAtW 16 σ.mem (σ.gpr .rcx) L.k).map ntt

/-- `NTT⁻¹(Â^⊺ ∘ ŷ)` and `NTT⁻¹(t̂^⊺ ∘ ŷ)`, from the inputs on entry. -/
abbrev prods (L : Kem) (σ : State) : List Poly :=
  ((mulMatTVec L.k (matAtW 16 σ.mem (σ.gpr .rsi) L.k) (yHat L σ)).map nttInv) ++
    [nttInv (dot (decodeVec L.k (tB L σ)) (yHat L σ))]

/-- After the products: the first `nu` of `u` are in `ct`, and the products from `nu` in place. -/
structure EU (L : Kem) (σ : State) (nu : Nat) (s : State) : Prop where
  kt : KT L σ s
  w : ∀ i < L.k + 1, nu ≤ i →
    PolyIs s.mem (σ.gpr .r9 + BitVec.ofNat 64 (oQ (2 * L.k + i))) ((prods L σ).getD i zero)
  u : ∀ i < nu, bytesAt s.mem (σ.gpr .rdi + BitVec.ofNat 64 (32 * L.du * i)) (32 * L.du) =
    compressEncode L.du (add ((prods L σ).getD i zero) (rW σ (L.k + i)))

omit E in
theorem q_add (b i : Nat) :
    σ.gpr .r9 + BitVec.ofNat 64 (oQ b) + BitVec.ofNat 64 (1024 * i) = σ.gpr .r9 + BitVec.ofNat 64 (oQ (b + i)) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  congr 2
  simp only [oQ]; omega

omit E in
theorem off_add (p : Addr) (a b : Nat) : p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem KT.mat {s : State} (h : KT L σ s) :
    matAtW 16 s.mem (σ.gpr .rsi) L.k = matAtW 16 σ.mem (σ.gpr .rsi) L.k := by
  simp only [matAtW, vecAtW]
  refine List.map_congr_left fun i hi => List.map_congr_left fun j hj => ?_
  have hi := List.mem_range.mp hi
  have hj := List.mem_range.mp hj
  have he : L.k * i + j < L.k * L.k :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj _) (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi)
  rw [off_add, show 32 * 16 * (L.k * i) + 32 * 16 * j = 512 * (L.k * i + j) by omega]
  exact (h.aW E he).2

theorem mul_ok (W : KeWf L) {mul : Nat → Prog isa}
    (hv : ∀ s, (encMulK16 L.k).pre s → ∃ t s', Exec isa (mul L.k) s t s' ∧ abiPreserved s s' ∧
      (encMulK16 L.k).post s s')
    (hn : (mul L.k).noCalls = true) {s : State} (h : ER L σ L.k L.k s) :
    WP isa (prodE L mul) s (EU L σ 0) := by
  have hkt := h.kt
  have hk4 : L.k ≤ 4 := by rcases W.k34 with e | e <;> omega
  have hkk : 0 < 512 * (L.k * L.k) := by rcases W.k34 with e | e <;> rw [e] <;> decide
  have eU := pa_q hkt (2 * L.k)
  have eT := pa_q hkt L.k
  have eY := pa_q hkt 0
  have eA : pa s ((.rbp, 0) : Ptr) = σ.gpr .rsi := by simp only [pa, hkt.rbp, add_ofNat_zero]
  have eZ : pa s ((.rbx, 0) : Ptr) = σ.gpr .r9 := by simp only [pa, hkt.rbx, add_ofNat_zero]
  have nS := E.nS
  have od : ∀ {a n b m : Nat}, a + n ≤ b ∨ b + m ≤ a → a + n ≤ kScrE → b + m ≤ kScrE →
      Region.Disjoint ⟨σ.gpr .r9 + BitVec.ofNat 64 a, n⟩ ⟨σ.gpr .r9 + BitVec.ofNat 64 b, m⟩ :=
    fun h1 h2 h3 => Offset.disjoint _ h1 (by simp only [kScrE] at h2; omega) (by simp only [kScrE] at h3; omega)
  have od0 : ∀ {a n : Nat}, 4096 ≤ a → a + n ≤ kScrE →
      Region.Disjoint ⟨σ.gpr .r9 + BitVec.ofNat 64 a, n⟩ (cR (σ.gpr .r9)) := fun {a n} h1 h2 => by
    have := od (a := a) (n := n) (b := 0) (m := 4096) (.inr h1) h2 (by decide)
    rwa [add_ofNat_zero] at this
  have sV : ∀ {a n : Nat}, a + n ≤ oTop → Region.Sub ⟨σ.gpr .r9 + BitVec.ofNat 64 a, n⟩ ⟨σ.gpr .r9, oTop⟩ :=
    fun ha => Offset.sub_base _ ha
  have sC : Region.Sub (cR (σ.gpr .r9)) ⟨σ.gpr .r9, oTop⟩ := Region.sub_prefix (by decide)
  have sS : ∀ {r : Region}, Region.Sub r ⟨σ.gpr .r9, oTop⟩ → Region.Sub r ⟨σ.gpr .r9, kScrE⟩ :=
    fun hr x hx => sub_top x (hr x hx)
  have bU : oQ (2 * L.k) + 1024 * (L.k + 1) ≤ oTop := by simp only [oQ, oTop]; omega_using [hk4]
  have bT : oQ L.k + 1024 * L.k ≤ oTop := by simp only [oQ, oTop]; omega_using [hk4]
  have bY : oQ 0 + 1024 * L.k ≤ oTop := by simp only [oQ, oTop]; omega_using [hk4]
  have cA : Covers [⟨σ.gpr .rsi, 512 * (L.k * L.k)⟩] (s.rd ++ s.wr) := by
    have := covers_one (inA E hkt (o := 0) (n := 512 * (L.k * L.k)) (by omega) hkk)
    rwa [add_ofNat_zero] at this
  have cZ : ∀ {X : List Region}, (∀ {o n : Nat}, o + n ≤ kScrE → InRegions X (σ.gpr .r9 + BitVec.ofNat 64 o) n) →
      Covers [cR (σ.gpr .r9)] X := fun hX => by
    have := covers_one (hX (o := 0) (n := 4096) (by decide))
    rwa [add_ofNat_zero] at this
  refine WP.mono (glueIn_ok hv hn (emGlue_ok (qP (2 * L.k)) (.rbp, 0) (qP L.k) (qP 0) (.rbx, 0)
      ⟨by simp only [oQ]; omega_using [hk4], by decide, by simp only [oQ]; omega_using [hk4], by simp only [oQ]; omega_using [hk4], by decide⟩
      (by simp [NA, argRegs]) (na_rbx _) (na_rbx _) (na_rbx _) s)
    (rd := [⟨σ.gpr .rsi, 512 * (L.k * L.k)⟩, vR (σ.gpr .r9 + BitVec.ofNat 64 (oQ L.k)) L.k,
      vR (σ.gpr .r9 + BitVec.ofNat 64 (oQ 0)) L.k])
    (wr := [vR (σ.gpr .r9 + BitVec.ofNat 64 (oQ (2 * L.k))) (L.k + 1), cR (σ.gpr .r9)])
    (fun s1 hV hm k1 => ?_) ?_ ?_) fun s' ⟨hP, s1, hV, hm, k1, hq⟩ => ?_
  · simp only [encMulK16, encMulKA, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_mem, hV.1, hV.2.1, hV.2.2.1, hV.2.2.2.1, hV.2.2.2.2, hm, eU, eT, eY, eA, eZ]
    have rS := fun {R : Region} (hR : Region.Sub R ⟨σ.gpr .r9, kScrE⟩) =>
      retR_keep k1 (by rw [retR_eq hkt]; exact E.xS.sub_right hR) [⟨σ.gpr .rsi, 512 * (L.k * L.k)⟩,
        vR (σ.gpr .r9 + BitVec.ofNat 64 (oQ L.k)) L.k, vR (σ.gpr .r9 + BitVec.ofNat 64 (oQ 0)) L.k]
        [vR (σ.gpr .r9 + BitVec.ofNat 64 (oQ (2 * L.k))) (L.k + 1), cR (σ.gpr .r9)]
    refine ⟨trivial, trivial, E.aS.symm.sub_left (sS (sV bU)),
      od (by simp only [oQ]; omega_using [hk4]) (by simp only [oQ, kScrE]; omega_using [hk4]) (by simp only [oQ, kScrE]; omega_using [hk4]),
      od (by simp only [oQ]; omega_using [hk4]) (by simp only [oQ, kScrE]; omega_using [hk4]) (by simp only [oQ, kScrE]; omega_using [hk4]),
      od0 (by simp only [oQ]; omega_using [hk4]) (by simp only [oQ, kScrE]; omega_using [hk4]), E.aS.sub_right (sS sC),
      od0 (by simp only [oQ]; omega_using [hk4]) (by simp only [oQ, kScrE]; omega_using [hk4]),
      od0 (by simp only [oQ]; omega_using [hk4]) (by simp only [oQ, kScrE]; omega_using [hk4]),
      rS (sS (sV bU)), retR_keep k1 (by rw [retR_eq hkt]; exact E.xA) _ _, rS (sS (sV bT)), rS (sS (sV bY)),
      rS (sS sC), fun e he => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · rw [show 32 * 16 * e = 512 * e by omega]; exact (hkt.aW E he).1
    · rw [q_add]; exact (h.t i hi).1
    · rw [q_add, Nat.zero_add]; exact (h.y i hi).1
  · exact covers_append (covers_cons cA (covers_cons (covers_one (inS' E hkt (by simp only [oQ, kScrE]; omega_using [hk4])))
      (covers_cons (covers_one (inS' E hkt (by simp only [oQ, kScrE]; omega_using [hk4]))) covers_nil)))
      (covers_cons (covers_one (inS' E hkt (by simp only [oQ, kScrE]; omega_using [hk4]))) (covers_cons (cZ (inS' E hkt))
        covers_nil))
  · exact covers_cons (covers_one (inS E hkt (by simp only [oQ, kScrE]; omega_using [hk4]))) (covers_cons (cZ (inS E hkt))
      covers_nil)
  simp only [encMulK16, encMulKA, State.withRegions_gpr, State.withRegions_mem, hV.1, hV.2.1, hV.2.2.1,
    hV.2.2.2.1, hm, eU, eT, eY, eA] at hq
  have hy : (vecAt s.mem (σ.gpr .r9 + BitVec.ofNat 64 (oQ 0)) L.k).map ntt = yHat L σ := by
    simp only [vecAt, yHat, vecAtW, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    simp only [Function.comp_apply]
    rw [q_add, Nat.zero_add, (h.y j (List.mem_range.mp hj)).2, show 32 * 16 * j = 512 * j by omega]
  have ht : vecAt s.mem (σ.gpr .r9 + BitVec.ofNat 64 (oQ L.k)) L.k = decodeVec L.k (tB L σ) := by
    rw [← List.take_of_length_le (l := tB L σ) (i := 384 * L.k) (by rw [bytesAt_length]), KPke.decodeVec_take]
    simp only [vecAt]
    exact List.map_congr_left fun j hj => by rw [q_add]; exact (h.t j (List.mem_range.mp hj)).2
  rw [hy, ht, hkt.mat E] at hq
  refine ⟨hkt.step E hP fun r hr => ?_, fun i hi _ => ?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [.inl (sV bU), .inl sC]
  · rw [← q_add]; exact hq.2 i hi

/-! ## `u` and `v` -/

omit E in
theorem EU.keepW {nu : Nat} {s s' : State} (h : EU L σ nu s) {W : List Region} (hP : IPost s s' W) {i : Nat} (hi : i < L.k + 1)
    (hd : ∀ r ∈ W, (pR (σ.gpr .r9 + BitVec.ofNat 64 (oQ (2 * L.k + i)))).Disjoint r) (hn : nu ≤ i) :
    PolyIs s'.mem (σ.gpr .r9 + BitVec.ofNat 64 (oQ (2 * L.k + i))) ((prods L σ).getD i zero) :=
  polyIs_frame hP.frame hd (h.w i hi hn)

omit E in
theorem pa_r15 {s : State} (h : KT L σ s) (o : Nat) : pa s (.r15, o) = σ.gpr .rdi + BitVec.ofNat 64 o := by
  simp only [pa, h.r15]

theorem u_ok {A : Arith} {wc wd : List Nat} (K : KemCalls L wc wd) (W : KeWf L)
    (hnC : (L.ce A.codecs).noCalls = true) {i : Nat} (hi : i < L.k) {s : State}
    (h : EU L σ i s) : WP isa (uE L A i) s (EU L σ (i + 1)) := by
  have hkt := h.kt
  have hk4 : L.k ≤ 4 := by rcases W.k34 with e | e <;> omega
  have hct := W.ct
  have hdu := W.du
  have bnd := Decaps.uSlice_le L hi
  have bR : 512 * (L.k + i) + 512 ≤ 512 * (2 * L.k + 1) := by omega
  -- `u[i]`
  have e1 : pa s ((.r13, 512 * (L.k + i)) : Ptr) = σ.gpr .rcx + BitVec.ofNat 64 (512 * (L.k + i)) := by
    simp only [pa, hkt.r13]
  have eF := pa_q hkt (2 * L.k + i)
  have hw0 := h.w i (by omega) (Nat.le_refl _)
  have hR := hkt.rW E (i := L.k + i) (by omega)
  have HA : Add16Hi (qP (2 * L.k + i)) (.r13, 512 * (L.k + i)) s :=
    { off := ⟨by simp only [oQ]; omega, by omega⟩
      redF := by rw [eF]; exact hw0.1
      redG := by rw [e1]; exact hR.1
      d := by rw [eF, e1]; exact (E.rS.symm.sub_left (qScr (by omega))).sub_right (Offset.sub_base _ bR)
      rF := by rw [retR_eq hkt, eF]; exact E.xS.sub_right (qScr (by omega))
      rG := by rw [retR_eq hkt, e1]; exact E.xR.sub_right (Offset.sub_base _ bR)
      c := by
        rw [eF, e1]
        exact covers_append (covers_one (inR E hkt bR)) (covers_one (inS' E hkt (by simp only [oQ, kScrE]; omega)))
      w := by rw [eF]; exact covers_one (inS E hkt (by simp only [oQ, kScrE]; omega)) }
  refine WP.seq (WP.mono (add16In_ok (by simp) HA) fun s2 ⟨hP2, hq2⟩ => ?_)
  rw [eF, e1, hw0.2, hR.2] at hq2
  rw [eF] at hP2
  have kt2 := hkt.step E hP2 fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact .inl (qSub (by omega))
  -- to `ct`
  have eQ := pa_q kt2 (2 * L.k + i)
  have eO := pa_r15 kt2 (32 * L.du * i)
  have HC : CEHi wc (qP (2 * L.k + i)) (.r15, 32 * L.du * i) L.du s2 :=
    { off := ⟨by simp only [oQ]; omega, by omega⟩
      dw := K.du.1
      red := by rw [eQ]; exact hq2.1
      dj := by rw [eQ, eO]; exact (E.cS.symm.sub_left (qScr (by omega))).sub_right (Offset.sub_base _ bnd)
      rF := by rw [retR_eq kt2, eQ]; exact E.xS.sub_right (qScr (by omega))
      rO := by rw [retR_eq kt2, eO]; exact E.xC.sub_right (Offset.sub_base _ bnd)
      c := by
        rw [eQ, eO]
        exact covers_append (covers_one (inS' E kt2 (by simp only [oQ, kScrE]; omega)))
          (covers_one (inCt' E kt2 bnd (by omega)))
      w := by rw [eO]; exact covers_one (inCt E kt2 bnd (by omega)) }
  refine WP.mono (ceIn_ok (K.ce A.codecs) hnC (by simp [NA, argRegs]) HC) fun s3 ⟨hP3, hq3⟩ => ?_
  rw [eO] at hP3 hq3
  rw [eQ, hq2.2] at hq3
  have kt3 := kt2.step E hP3 fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact .inr (Offset.sub_base _ bnd)
  have dC : ∀ {a : Nat}, a < 14 → ∀ r ∈ [(⟨σ.gpr .rdi + BitVec.ofNat 64 (32 * L.du * i), 32 * L.du⟩ : Region)],
      (pR (σ.gpr .r9 + BitVec.ofNat 64 (oQ a))).Disjoint r := fun ha r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact (E.cS.symm.sub_left (qScr ha)).sub_right (Offset.sub_base _ bnd)
  refine ⟨kt3, fun i' hi' hn => ?_, fun i' hi' => ?_⟩
  · refine polyIs_frame hP3.frame (dC (by omega)) (polyIs_frame hP2.frame ?_ (h.w i' hi' (by omega)))
    intro r hr; rw [List.mem_singleton] at hr; subst hr
    exact qDisj E (by omega) (by omega) (by omega)
  · rcases (by omega : i' < i ∨ i' = i) with hi'' | rfl
    · have bnd' := Decaps.uSlice_le L (i := i') (by omega)
      have dj : Region.Disjoint ⟨σ.gpr .rdi + BitVec.ofNat 64 (32 * L.du * i'), 32 * L.du⟩
          ⟨σ.gpr .rdi + BitVec.ofNat 64 (32 * L.du * i), 32 * L.du⟩ :=
        Offset.disjoint _ (.inl (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi'')) (by omega) (by omega)
      have dq : ∀ {a : Nat}, a < 14 → ∀ r ∈ [pR (σ.gpr .r9 + BitVec.ofNat 64 (oQ a))],
          Region.Disjoint ⟨σ.gpr .rdi + BitVec.ofNat 64 (32 * L.du * i'), 32 * L.du⟩ r := fun ha r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact (E.cS.sub_left (Offset.sub_base _ bnd')).sub_right (qScr ha)
      rw [bytesAt_frame hP3.frame (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact dj) (by omega),
        bytesAt_frame hP2.frame (dq (by omega)) (by omega)]
      exact h.u i' hi''
    · exact hq3


omit E in
/-- `k` consecutive pieces of `c` bytes. -/
theorem bytesAt_cat (m : Mem) (p : Addr) (c : Nat) (f : Nat → List Byte) :
    ∀ k, (∀ i < k, bytesAt m (p + BitVec.ofNat 64 (c * i)) c = f i) → bytesAt m p (c * k) = (List.range k).flatMap f
  | 0, _ => rfl
  | k + 1, h => by
    rw [Nat.mul_succ, bytesAt_add, bytesAt_cat m p c f k fun i hi => h i (by omega), h k (by omega),
      List.range_succ, List.flatMap_append, List.flatMap_singleton]

omit E in
theorem flatMap_congr {α β : Type} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h a (List.mem_cons_self ..),
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

omit E in
theorem list_eq_map_getD {X : List Poly} {k : Nat} (h : X.length = k) :
    X = (List.range k).map fun i => X.getD i zero := by
  subst h
  refine List.ext_getElem (by simp) fun n h1 h2 => ?_
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]

omit E in
/-- The ciphertext, from its pieces. -/
theorem ct_eq {m : Mem}
    (hu : ∀ i < L.k, bytesAt m (σ.gpr .rdi + BitVec.ofNat 64 (32 * L.du * i)) (32 * L.du) =
      compressEncode L.du (add ((prods L σ).getD i zero) (rW σ (L.k + i))))
    (hv : bytesAt m (σ.gpr .rdi + BitVec.ofNat 64 (32 * L.du * L.k)) (32 * L.dv) =
      compressEncode L.dv (add (add ((prods L σ).getD L.k zero) (rW σ (2 * L.k)))
        (decodeDecompress 1 (bytesAt σ.mem (σ.gpr .r8) 32)))) :
    bytesAt m (σ.gpr .rdi) L.ctLen = encCt L σ.mem (σ.gpr .rsi) (σ.gpr .rdx) (σ.gpr .rcx) (σ.gpr .r8) := by
  have hX : ((mulMatTVec L.k (matAtW 16 σ.mem (σ.gpr .rsi) L.k) (yHat L σ)).map nttInv).length = L.k := by
    simp [mulMatTVec]
  have hP : ∀ i < L.k, (prods L σ).getD i zero =
      ((mulMatTVec L.k (matAtW 16 σ.mem (σ.gpr .rsi) L.k) (yHat L σ)).map nttInv).getD i zero := fun i hi => by
    simp only [prods, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hX]; exact hi)]
  have hPk : (prods L σ).getD L.k zero = nttInv (dot (decodeVec L.k (tB L σ)) (yHat L σ)) := by
    rw [prods, List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hX]), hX, Nat.sub_self,
      List.getElem?_cons_zero, Option.getD_some]
  rw [show L.ctLen = 32 * L.du * L.k + 32 * L.dv by
      simp only [Kem.ctLen, Params.ctLen, Kem.du, Kem.dv, Kem.k]; rw [Nat.mul_add, Nat.mul_assoc],
    bytesAt_add, hv, hPk, bytesAt_cat m _ (32 * L.du) _ L.k hu]
  simp only [encCt]
  rw [list_eq_map_getD hX, vecAtW, KPke.addVec_map, List.flatMap_map]
  refine congr (congrArg HAppend.hAppend (flatMap_congr fun i hi => ?_)) ?_
  · rw [hP i (List.mem_range.mp hi), rW, off_add, show 512 * L.k + 32 * 16 * i = 512 * (L.k + i) by omega]
  · rw [rW, show 512 * (2 * L.k) = 1024 * L.k by omega]

theorem v_ok {A : Arith} (hA : ArithOk A) {wc wd : List Nat} (K : KemCalls L wc wd) (W : KeWf L)
    (hnA : A.add.noCalls = true) (hnC : (L.ce A.codecs).noCalls = true) (hnD : A.codecs.dd.noCalls = true)
    {s : State} (h : EU L σ L.k s) :
    WP isa (vE L A) s fun s' => KT L σ s' ∧
      bytesAt s'.mem (σ.gpr .rdi) L.ctLen = encCt L σ.mem (σ.gpr .rsi) (σ.gpr .rdx) (σ.gpr .rcx) (σ.gpr .r8) := by
  have hkt := h.kt
  have hk4 : L.k ≤ 4 := by rcases W.k34 with e | e <;> omega
  have hct := W.ct
  have hdv := W.dv
  have hdu := W.du
  have bnd : 32 * L.du * L.k + 32 * L.dv ≤ L.ctLen := by
    simp only [Kem.ctLen, Params.ctLen, Kem.du, Kem.dv, Kem.k]; rw [Nat.mul_add, ← Nat.mul_assoc]
  have bR : 512 * (2 * L.k) + 512 ≤ 512 * (2 * L.k + 1) := by omega
  have e3 : 2 * L.k + L.k = 3 * L.k := by omega
  -- `NTT⁻¹(t̂^⊺ ∘ ŷ) + e₂`
  have e1 : pa s ((.r13, 512 * (2 * L.k)) : Ptr) = σ.gpr .rcx + BitVec.ofNat 64 (512 * (2 * L.k)) := by
    simp only [pa, hkt.r13]
  have eF := pa_q hkt (3 * L.k)
  have hw0 := h.w L.k (by omega) (Nat.le_refl _)
  rw [e3] at hw0
  have hR := hkt.rW E (i := 2 * L.k) (by omega)
  have HA2 : Add16Hi (qP (3 * L.k)) (.r13, 512 * (2 * L.k)) s :=
    { off := ⟨by simp only [oQ]; omega, by omega⟩
      redF := by rw [eF]; exact hw0.1
      redG := by rw [e1]; exact hR.1
      d := by rw [eF, e1]; exact (E.rS.symm.sub_left (qScr (by omega))).sub_right (Offset.sub_base _ bR)
      rF := by rw [retR_eq hkt, eF]; exact E.xS.sub_right (qScr (by omega))
      rG := by rw [retR_eq hkt, e1]; exact E.xR.sub_right (Offset.sub_base _ bR)
      c := by
        rw [eF, e1]
        exact covers_append (covers_one (inR E hkt bR)) (covers_one (inS' E hkt (by simp only [oQ, kScrE]; omega)))
      w := by rw [eF]; exact covers_one (inS E hkt (by simp only [oQ, kScrE]; omega)) }
  have dQ : ∀ {a b : Nat}, a < 14 → b < 14 → a ≠ b →
      ∀ r ∈ [pR (σ.gpr .r9 + BitVec.ofNat 64 (oQ b))], (pR (σ.gpr .r9 + BitVec.ofNat 64 (oQ a))).Disjoint r :=
    fun ha hb hne r hr => by rw [List.mem_singleton] at hr; subst hr; exact qDisj E ha hb hne
  have dC : ∀ {a : Nat}, a < 14 → ∀ i < L.k, ∀ r ∈ [pR (σ.gpr .r9 + BitVec.ofNat 64 (oQ a))],
      Region.Disjoint ⟨σ.gpr .rdi + BitVec.ofNat 64 (32 * L.du * i), 32 * L.du⟩ r := fun ha i hi r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact (E.cS.sub_left (Offset.sub_base _ (Decaps.uSlice_le L hi))).sub_right (qScr ha)
  refine WP.seq (WP.mono (add16In_ok (by simp) HA2) fun s2 ⟨hP2, hq2⟩ => ?_)
  rw [eF, e1, hw0.2, hR.2] at hq2
  rw [eF] at hP2
  have kt2 := hkt.step E hP2 fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact .inl (qSub (by omega))
  have hu2 : ∀ i < L.k, bytesAt s2.mem (σ.gpr .rdi + BitVec.ofNat 64 (32 * L.du * i)) (32 * L.du) =
      compressEncode L.du (add ((prods L σ).getD i zero) (rW σ (L.k + i))) := fun i hi => by
    rw [bytesAt_frame hP2.frame (dC (by omega) i hi) (by omega)]; exact h.u i hi
  have HA : ∀ {s : State}, KT L σ s → Reduced s.mem (σ.gpr .r9 + BitVec.ofNat 64 (oQ (3 * L.k))) →
      Reduced s.mem (σ.gpr .r9 + BitVec.ofNat 64 (oQ (3 * L.k + 1))) → AccHi (qP (3 * L.k)) (eP L) s :=
    fun {s} kt rf rg =>
    { off := ⟨by simp only [oQ]; omega, by simp only [oQ]; omega⟩
      redF := by rw [pa_q kt]; exact rf
      redG := by rw [pa_q kt]; exact rg
      d := by rw [pa_q kt, pa_q kt]; exact qDisj E (by omega) (by omega) (by omega)
      rF := by rw [retR_eq kt, pa_q kt]; exact E.xS.sub_right (qScr (by omega))
      rG := by rw [retR_eq kt, pa_q kt]; exact E.xS.sub_right (qScr (by omega))
      c := by
        rw [pa_q kt, pa_q kt]
        exact covers_append (covers_one (inS' E kt (by simp only [oQ, kScrE]; omega)))
          (covers_one (inS' E kt (by simp only [oQ, kScrE]; omega)))
      w := by rw [pa_q kt]; exact covers_one (inS E kt (by simp only [oQ, kScrE]; omega)) }
  -- `μ`
  have eB : pa s2 ((.r14, 0) : Ptr) = σ.gpr .r8 + BitVec.ofNat 64 0 := by simp only [pa, kt2.r14]
  have eE2 := pa_q kt2 (3 * L.k + 1)
  have bM : 0 + 32 * 1 ≤ 32 := by decide
  have HD : DDHi compressWidths (.r14, 0) (eP L) 1 s2 :=
    { off := ⟨by decide, by simp only [oQ]; omega⟩
      dw := by decide
      dj := by rw [eB, eE2]; exact (E.mS.sub_left (Offset.sub_base _ bM)).sub_right (qScr (by omega))
      rB := by rw [retR_eq kt2, eB]; exact E.xM.sub_right (Offset.sub_base _ bM)
      rF := by rw [retR_eq kt2, eE2]; exact E.xS.sub_right (qScr (by omega))
      c := by
        rw [eB, eE2]
        exact covers_append (covers_one (inM E kt2 bM)) (covers_one (inS' E kt2 (by simp only [oQ, kScrE]; omega)))
      w := by rw [eE2]; exact covers_one (inS E kt2 (by simp only [oQ, kScrE]; omega)) }
  refine WP.seq (WP.mono (ddIn_ok (Codecs.ddI A.codecs) hnD (na_rbx _) HD) fun s3 ⟨hP3, hq3⟩ => ?_)
  rw [eE2] at hP3 hq3
  rw [eB, add_ofNat_zero, show 32 * 1 = 32 from rfl, kt2.bM E] at hq3
  have kt3 := kt2.step E hP3 fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact .inl (qSub (by omega))
  have hv3 := polyIs_frame hP3.frame (dQ (by omega) (by omega) (by omega)) hq2
  have hu3 : ∀ i < L.k, bytesAt s3.mem (σ.gpr .rdi + BitVec.ofNat 64 (32 * L.du * i)) (32 * L.du) =
      compressEncode L.du (add ((prods L σ).getD i zero) (rW σ (L.k + i))) := fun i hi => by
    rw [bytesAt_frame hP3.frame (dC (by omega) i hi) (by omega)]; exact hu2 i hi
  -- `v`
  have eF3 := pa_q kt3 (3 * L.k)
  have eG3 := pa_q kt3 (3 * L.k + 1)
  refine WP.seq (WP.mono (accIn_ok hA.add.ok hnA (g := eP L) (by simp) (HA kt3 hv3.1 hq3.1)) fun s4 ⟨hP4, hq4⟩ => ?_)
  rw [eF3, eG3, hv3.2, hq3.2] at hq4
  rw [eF3] at hP4
  have kt4 := kt3.step E hP4 fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact .inl (qSub (by omega))
  have hu4 : ∀ i < L.k, bytesAt s4.mem (σ.gpr .rdi + BitVec.ofNat 64 (32 * L.du * i)) (32 * L.du) =
      compressEncode L.du (add ((prods L σ).getD i zero) (rW σ (L.k + i))) := fun i hi => by
    rw [bytesAt_frame hP4.frame (dC (by omega) i hi) (by omega)]; exact hu3 i hi
  -- to `ct`
  have eQ := pa_q kt4 (3 * L.k)
  have eO := pa_r15 kt4 (32 * L.du * L.k)
  have HC : CEHi wc (qP (3 * L.k)) (.r15, 32 * L.du * L.k) L.dv s4 :=
    { off := ⟨by simp only [oQ]; omega, by omega⟩
      dw := K.dv.1
      red := by rw [eQ]; exact hq4.1
      dj := by rw [eQ, eO]; exact (E.cS.symm.sub_left (qScr (by omega))).sub_right (Offset.sub_base _ bnd)
      rF := by rw [retR_eq kt4, eQ]; exact E.xS.sub_right (qScr (by omega))
      rO := by rw [retR_eq kt4, eO]; exact E.xC.sub_right (Offset.sub_base _ bnd)
      c := by
        rw [eQ, eO]
        exact covers_append (covers_one (inS' E kt4 (by simp only [oQ, kScrE]; omega)))
          (covers_one (inCt' E kt4 bnd (by omega)))
      w := by rw [eO]; exact covers_one (inCt E kt4 bnd (by omega)) }
  refine WP.mono (ceIn_ok (K.ce A.codecs) hnC (by simp [NA, argRegs]) HC) fun s5 ⟨hP5, hq5⟩ => ?_
  rw [eO] at hP5 hq5
  rw [eQ, hq4.2] at hq5
  refine ⟨kt4.step E hP5 fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact .inr (Offset.sub_base _ bnd), ct_eq (fun i hi => ?_) hq5⟩
  rw [bytesAt_frame hP5.frame (fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inl (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi))
      (by have := Decaps.uSlice_le L hi; omega) (by omega)) (by omega)]
  exact hu4 i hi

end

/-! ## The function -/

/-- The prologue, `t̂`, `y` and the products. -/
theorem pre_wp {L : Kem} {A : Arith} (hA : ArithOk A) (W : KeWf L) {mul : Nat → Prog isa}
    (hv : ∀ s, (encMulK16 L.k).pre s → ∃ t s', Exec isa (mul L.k) s t s' ∧ abiPreserved s s' ∧
      (encMulK16 L.k).post s s')
    (hn : (mul L.k).noCalls = true) (hn12 : A.dec12.noCalls = true) {σ : State} (hp : (kpkeEncK L).pre σ) :
    WP isa (kpkeEncPre L A mul) σ (EU L σ 0) := by
  have E := ep hp
  refine WP.seq (WP.mono (pro_ok E) fun s₁ h₁ => ?_)
  have d₀ : ER L σ 0 0 s₁ :=
    ⟨h₁, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  refine WP.seq (WP.mono (seqR_ok (I := fun i s => ER L σ i 0 s) L.k 0
    (fun i _ hi s h => t_ok E hA W hn12 (by omega) h) s₁ d₀) fun s₂ h₂ => ?_)
  rw [Nat.zero_add] at h₂
  refine WP.seq (WP.mono (seqR_ok (I := fun j s => ER L σ L.k j s) L.k 0
    (fun j _ hj s h => y_ok E W (by omega) h) s₂ h₂) fun s₃ h₃ => ?_)
  rw [Nat.zero_add] at h₃
  exact mul_ok E W hv hn h₃

/-- `u`, `v` and the epilogue. -/
theorem post_wp {L : Kem} {A : Arith} (hA : ArithOk A) {wc wd : List Nat} (K : KemCalls L wc wd)
    (W : KeWf L) (hnA : A.add.noCalls = true) (hnC : (L.ce A.codecs).noCalls = true)
    (hnD : A.codecs.dd.noCalls = true) {σ : State} (hp : (kpkeEncK L).pre σ) {s : State} (h : EU L σ 0 s) :
    WP isa (kpkeEncPost L A) s fun s' => gprPreserved σ s' ∧ (kpkeEncK L).post σ s' := by
  have E := ep hp
  refine WP.seq (WP.mono (seqR_ok (I := fun i s => EU L σ i s) L.k 0
    (fun i _ hi s h => u_ok E K W hnC (by omega) h) s h) fun s₅ h₅ => ?_)
  rw [Nat.zero_add] at h₅
  exact WP.seq (WP.mono (v_ok E hA K W hnA hnC hnD h₅) fun s₆ ⟨kt₆, hm₆⟩ =>
    WP.mono (epi_ok E kt₆) fun s₇ ⟨hg, hm⟩ => ⟨hg, by show bytesAt _ _ _ = _; rw [hm]; exact hm₆⟩)

theorem kpkeEnc_wp {L : Kem} {A : Arith} (hA : ArithOk A) {wc wd : List Nat} (K : KemCalls L wc wd)
    (W : KeWf L) {mul : Nat → Prog isa}
    (hv : ∀ s, (encMulK16 L.k).pre s → ∃ t s', Exec isa (mul L.k) s t s' ∧ abiPreserved s s' ∧
      (encMulK16 L.k).post s s')
    (hn : (mul L.k).noCalls = true) (hn12 : A.dec12.noCalls = true) (hnA : A.add.noCalls = true)
    (hnC : (L.ce A.codecs).noCalls = true) (hnD : A.codecs.dd.noCalls = true)
    {σ : State} (hp : (kpkeEncK L).pre σ) :
    WP isa (kpkeEnc L A mul) σ fun s' => gprPreserved σ s' ∧ (kpkeEncK L).post σ s' :=
  WP.seq (WP.mono (pre_wp hA W hv hn hn12 hp) fun _ h => post_wp hA K W hnA hnC hnD hp h)

theorem kpkeEnc_correct {L : Kem} {A : Arith} (hA : ArithOk A) {wc wd : List Nat} (K : KemCalls L wc wd)
    (W : KeWf L) {mul : Nat → Prog isa}
    (hv : ∀ s, (encMulK16 L.k).pre s → ∃ t s', Exec isa (mul L.k) s t s' ∧ abiPreserved s s' ∧
      (encMulK16 L.k).post s s')
    (hn : (mul L.k).noCalls = true) (hn12 : A.dec12.noCalls = true) (hnA : A.add.noCalls = true)
    (hnC : (L.ce A.codecs).noCalls = true) (hnD : A.codecs.dd.noCalls = true)
    (hctl : ctlOk (kpkeEnc L A mul) = true) (σ : State) (hp : (kpkeEncK L).pre σ) :
    ∃ t s', Exec isa (kpkeEnc L A mul) σ t s' ∧ abiPreserved σ s' ∧ (kpkeEncK L).post σ s' := by
  obtain ⟨t, s', he, hg, hq⟩ := kpkeEnc_wp hA K W hv hn hn12 hnA hnC hnD hp
  exact ⟨t, s', he, abiPreserved_of_ctl hctl he hg, hq⟩

end KpkeEnc

end VG.Proof.MlKem.X86_64

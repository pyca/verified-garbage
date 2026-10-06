import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain

/-!
# RSA with the CRT on x86-64: constant time of `q`'s phase

The start of a prime's phase (`unit_ct`, `unitPhase_ok`), its power
(`pow_ct`, `powPhase_ok`) and `q`'s phase (`qPhase_ct`, `qPhase_ok`), from
the claims about their parts (`GPowCT`, `RedcCT`, `ExpCT`). Between the
parts, each state predicate fixes the public data and keeps of the secrets
only what the next part's claim and the correctness of the parts after it
need.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

namespace CrtCTQ

/-- `Φ a` fixes `rdi`. -/
theorem pinsRdi {α : Type} {Φ : α → State → Prop} (f : α → Addr) (h : ∀ a s, Φ a s → s.gpr .rdi = f a) :
    Pins Φ [.rdi] :=
  pins_of (fun a _ => f a) fun a s hs r hr => by rw [List.mem_singleton.mp hr]; exact h a s hs

theorem gRanges_le (w : Nat) : ∀ r ∈ gRanges w, r.1 + r.2 ≤ slot w 8 := by
  have := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have := slot_le (w := w) (show Public.aAcc < 8 by decide)
  have := slot_le (w := w) (show Public.aTmp < 8 by decide)
  have := slot_le (w := w) (show Public.aY < 8 by decide)
  simp only [gRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl) <;> simp only [Crt.sD, Public.sCnt, sFn] <;> omega

theorem gxRanges_le {w o wx : Nat} (hlo : slot w 8 ≤ o) :
    ∀ r ∈ gRanges w ++ [xRange o wx], r.1 + r.2 ≤ o + slot wx 8 + tabBytes wx := by
  have hX8 : 8 * 17 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · have := gRanges_le w r hr; omega
  · rw [List.mem_singleton.mp hr]; simp only [xRange]; omega

/-- The modulus' header words but `sD`'s and `sCnt`'s, past a change within
`gRanges` and a prime's workspace. -/
theorem _root_.VG.Proof.Bignum.Frm.gx_hdr {m m' : Mem} {B : Addr} {w o wx : Nat} (hf : Frm B (gRanges w ++ [xRange o wx]) m m')
    (hlo : slot w 8 ≤ o) {i : Nat} (hi : i < 32) (h1 : i ≠ Crt.sD)
    (h2 : i ≠ Public.sCnt) : word m' B (8 * i) = word m B (8 * i) := by
  have := hdr_lt_slot w Public.aAcc hi
  have := hdr_lt_slot w Public.aTmp hi
  have := hdr_lt_slot w Public.aY hi
  have := hdr_lt_slot w 8 hi
  refine hf.word_eq (fun r hr => ?_) (by omega)
  simp only [gRanges, xRange, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · show 8 * i + 8 ≤ 8 * Crt.sD ∨ 8 * Crt.sD + 8 ≤ 8 * i
    unfold Crt.sD sFn at h1 ⊢; omega
  · show 8 * i + 8 ≤ 8 * Public.sCnt ∨ 8 * Public.sCnt + 8 ≤ 8 * i
    unfold Public.sCnt sFn at h2 ⊢; omega
  · exact Or.inl (by omega)

/-- A prime's workspace header past a change within `gRanges`. -/
theorem WsAt.of_g {m m' : Mem} {B : Addr} {w o wx : Nat} {mx : BitVec 64} (h : WsAt m B o wx mx)
    (hf : Frm B (gRanges w) m m') (hlo : slot w 8 ≤ o) (hoL : B.toNat + o + slot wx 8 ≤ 2 ^ 64) :
    WsAt m' B o wx mx :=
  h.of_words fun i hi => by
    have : 8 * 32 ≤ slot wx 8 := by unfold slot hdrBytes; omega
    rw [word_off, word_off]
    exact hf.word_eq (fun r hr => Or.inr (by have := gRanges_le w r hr; omega)) (by omega)

/-! ## The start of a prime's phase -/

/-- `gPow`'s public data. -/
def gp (p : UPub) : GPub := ⟨p.B, p.Z, p.w, p.minv, p.N, off p.B p.o, p.wx⟩

/-- The prime's workspace. -/
def xp (p : UPub) : XPub := ⟨p.B, p.Z, p.o, p.w, p.wx⟩

theorem gPre {sl : Nat} {p : UPub} {s : State} (h : UPre sl p s) : GPre sl (gp p) s := by
  obtain ⟨mx, X, hg, hw, hw28, hlo, hhi, hwx2, hwx, hsl, -, -, hslv, hws, hN, hodd, hN1, -⟩ := h
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot p.wx 8 := by unfold slot hdrBytes; omega
  dsimp only [GPre, gp]
  exact ⟨hg, by omega, by omega, by omega, hN.n, hN.inv, hodd, hN1, hN.r2, hN.one, hsl, hslv, hws.hdr.hw,
    (hs.sub (o := p.o) (n := slot p.wx 8) (by omega) (by omega)).ld (d := 8 * sW) (by unfold sW; omega), by omega, hwx⟩

/-- After `gPow`. -/
def U1 (sl : Nat) (p : UPub) (t : State) : Prop :=
  ∃ (mx : BitVec 64) (X : Nat), Good t p.B p.Z p.w p.minv ∧ p.w < 2 ^ 28 ∧ slot p.w 8 ≤ p.o ∧
    p.o + slot p.wx 8 + tabBytes p.wx ≤ p.Z ∧ 2 ≤ p.wx ∧ p.wx ≤ p.w ∧ sl < 32 ∧ word t.mem p.B (8 * sl) = off p.B p.o ∧
    WsAt t.mem p.B p.o p.wx mx ∧ XVals t p.B p.o p.wx mx X ∧ 1 < X

theorem gPow_u1 (M : Mont) {sl : Nat} {p : UPub} {s : State} (h : UPre sl p s) :
    WP isa (seqs (Crt.gPow M.mm sl)) s (U1 sl p) := by
  obtain ⟨mx, X, hg, hw, hw28, hlo, hhi, hwx2, hwx, hsl, hsl1, hsl2, hslv, hws, hN, hodd, hN1, hX, hX1, -⟩ := h
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot p.wx 8 := by unfold slot hdrBytes; omega
  have hoL : p.o + slot p.wx 8 ≤ 2 ^ 64 := by omega
  refine WP.mono (gPow_ok M hg (by omega) (by omega) (by omega) hN.n hN.inv hodd hN1 hN.r2 hN.one hsl hslv
    hws.hdr.hw ((hs.sub (o := p.o) (n := slot p.wx 8) (by omega) (by omega)).ld (d := 8 * sW) (by unfold sW; omega))
    (by omega) hwx) fun s₁ ⟨hg₁, _, _, f₁, _⟩ => ?_
  have f₁' : Frm p.B (gRanges p.w) s.mem s₁.mem := f₁
  have fx : Frm p.B (gRanges p.w ++ [xRange p.o p.wx]) s.mem s₁.mem :=
    Frm.mono f₁' fun r hr => List.mem_append_left _ hr
  exact ⟨mx, X, hg₁, hw28, hlo, hhi, hwx2, hwx, hsl, by rw [Frm.gx_hdr fx hlo hsl hsl1 hsl2]; exact hslv,
    WsAt.of_g hws f₁' hlo (by omega), hX.of_below f₁' (fun r hr => (gRanges_le _ r hr).trans hlo) hoL, hX1⟩

theorem blk_rpre {sl : Nat} {p : UPub} {s : State} (h : U1 sl p s) :
    WP isa (.block [.mov .rdi (.mem (hdr sl))]) s (RPre Public.aY (xp p)) := by
  obtain ⟨mx, X, hg, hw28, hlo, hhi, hwx2, hwx, hsl, hslv, hws, hX, hX1⟩ := h
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = off p.B p.o ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hs.ld (d := 8 * sl) (by omega), hslv]) rfl)
    fun t ⟨⟨hdi, hm⟩, k⟩ => ⟨mx, X, SubCtx.mk' (hs.congr k.2.2) (by rw [hm]; exact hg.hdr)
      (by rw [hm]; exact hws) hdi hlo hhi, ⟨by rw [hm]; exact hX.n, by rw [hm]; exact hX.inv,
      by rw [hm]; exact hX.one⟩, hwx2, hwx, (by omega : p.w < 2 ^ 30), hX1, by decide⟩

/-- A prime's workspace, its base in `rdi`, and its size. -/
def XG (p : XPub) (t : State) : Prop :=
  ∃ minv : BitVec 64, Good t (off p.B p.o) (slot p.wx 8) p.wx minv ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 30

/-- `Y := X_c` in a prime's workspace, and back to the modulus'. -/
theorem copyLeave_ct :
    RelCT isa (Two XG) (seqs (copyArr Public.aY aXc ++ ([.block [leave]] : List (Prog isa))))
      fun _ _ => True := by
  refine RelCT.seqs_append (by simp [copyArr]) (by simp) (RelCT.seq (two_post
    (Ψ := fun p t => t.gpr .rdi = off p.B p.o)
    (two_map (fun p : XPub => (⟨off p.B p.o, slot p.wx 8, p.wx⟩ : Ws))
      (fun _ _ ⟨minv, hg, _⟩ => ⟨minv, hg, Nat.le_refl _⟩)
      (copyArr_ct (by decide) (by decide) (by taint_decide)))
    fun p s ⟨_, hg, hwx2, hwx⟩ => WP.mono (copyArr_ok hg (Nat.le_refl _) (by omega) (by omega)
      (o := Public.aY) (a := aXc) (by decide) (by decide) (by decide))
      fun t ⟨_, _, k⟩ => (k.gpr (by decide)).trans hg.rdi) ?_)
  exact two_taint [.rdi] (pinsRdi (fun p : XPub => off p.B p.o) fun _ _ h => h) (by taint_decide)

/-- `redc`, `Y := X_c` and back to the modulus'. -/
theorem redcCopy_ct (M : Mont) (hR : RedcCT M Public.aY) :
    RelCT isa (Two (RPre Public.aY))
      (seqs (redc M.mm Public.aY ++ (copyArr Public.aY aXc ++ ([.block [leave]] : List (Prog isa)))))
      fun _ _ => True :=
  RelCT.seqs_append (by simp [redc]) (by simp [copyArr]) (RelCT.seq (two_post (Ψ := XG) hR
    fun _ _ ⟨minv, _, hc, hX, hwx2, hwx, hw30, hX1, hj⟩ =>
      WP.mono (redc_ok M hc hX hwx2 hwx hw30 hX1 hj) fun _ ⟨hc', _⟩ => ⟨minv, hc'.good, hwx2, by omega⟩)
    copyLeave_ct)

end CrtCTQ

open CrtCTQ in
/-- The start of a prime's phase is constant time. -/
theorem unit_ct (M : Mont) {sl : Nat} (hG : GPowCT M sl) (hR : RedcCT M Public.aY)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rdi (.mem (hdr sl))]) hc).isSome = true) :
    UnitCT M sl := by
  unfold UnitCT
  simp only [List.append_assoc]
  refine RelCT.seqs_append (by simp [Crt.gPow]) (by simp) (RelCT.seq (two_post (Ψ := U1 sl)
    (two_map gp (fun _ _ h => gPre h) hG) fun _ _ h => gPow_u1 M h) ?_)
  refine RelCT.seqs_append (by simp) (by simp [redc]) (RelCT.seq (two_piece
    (Ψ := fun p => RPre Public.aY (xp p)) [.rdi]
    (pinsRdi (fun p : UPub => p.B) fun _ _ ⟨_, _, hg, _⟩ => hg.rdi) hT fun _ _ h => blk_rpre h) ?_)
  exact two_map xp (fun _ _ h => h) (redcCopy_ct M hR)

namespace CrtCTQ

/-- After entering the prime's workspace. -/
def P1 (sd slen : Nat) (p : BPub) (t : State) : Prop :=
  ∃ (mx : BitVec 64) (X : Nat) (eb : List Byte), SubCtx t p.x.B p.x.Z p.x.o p.x.w p.x.wx mx ∧
    XVals t p.x.B p.x.o p.x.wx mx X ∧ 2 ≤ p.x.wx ∧ p.x.wx ≤ p.x.w ∧ p.x.w < 2 ^ 28 ∧ 1 < X ∧ X % 2 = 1 ∧
    wv t.mem (off p.x.B p.x.o) (slot p.x.wx Public.aY) p.x.wx < X ∧ sd < 32 ∧ slen < 32 ∧
    word t.mem p.x.B (8 * sd) = p.ptr ∧ word t.mem p.x.B (8 * slen) = BitVec.ofNat 64 eb.length ∧
    eb.length = p.len ∧ 1 ≤ eb.length ∧ eb.length ≤ 1024 ∧ Src t p.x.B p.x.Z p.ptr eb

theorem blk_p1 {sl sd slen : Nat} {p : BPub} {s : State} (h : PwPre sl sd slen p s) :
    WP isa (.block [.mov .rdi (.mem (hdr sl))]) s (P1 sd slen p) := by
  obtain ⟨_, mx, _, X, _, eb, hg, hw28, hlo, hhi, hwx2, hwx, hsl, hslv, hws, hX, hX1, hXodd, -, hyl, -, hsd, hsln,
    hep, hel, hlen, hL1, hL2, he⟩ := h
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot p.x.w 8 (show 31 < 32 by decide)
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = off p.x.B p.x.o ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hs.ld (d := 8 * sl) (by omega), hslv]) rfl)
    fun t ⟨⟨hdi, hm⟩, k⟩ => ⟨mx, X, eb, SubCtx.mk' (hs.congr k.2.2) (by rw [hm]; exact hg.hdr)
      (by rw [hm]; exact hws) hdi hlo hhi, ⟨by rw [hm]; exact hX.n, by rw [hm]; exact hX.inv,
      by rw [hm]; exact hX.one⟩, hwx2, hwx, hw28, hX1, hXodd, by rw [hm]; exact hyl, hsd, hsln,
      by rw [hm]; exact hep, by rw [hm]; exact hel, hlen, hL1, hL2,
      he.congrK (by rw [hm]; exact InScr.refl _ _ _) k⟩

theorem redc_ePre (M : Mont) {sd slen : Nat} {p : BPub} {s : State} (h : P1 sd slen p s) :
    WP isa (seqs (redc M.mm Public.aY)) s (EPre sd slen p) := by
  obtain ⟨mx, X, eb, hc, hX, hwx2, hwx, hw28, hX1, hXodd, hyl, hsd, hsln, hep, hel, hlen, hL1, hL2, he⟩ := h
  have hn := hc.scr.nowrap
  have hlo := hc.lo
  have hhi := hc.hi
  have h8 := hdr_lt_slot p.x.w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot p.x.wx 8 := by unfold slot hdrBytes; omega
  have ho64 : p.x.o < 2 ^ 64 := by omega
  have hoL : p.x.o + slot p.x.wx 8 ≤ 2 ^ 64 := by omega
  refine WP.mono (redc_ok M hc hX hwx2 hwx (by omega) hX1 (j := Public.aY) (by decide))
    fun t ⟨hc₂, hX₂, hlt₂, _, f₂, k₂⟩ => ?_
  have fx₂ : Frm p.x.B [xRange p.x.o p.x.wx] s.mem t.mem :=
    f₂.to_x (redcRanges_ok _) hoL (List.mem_singleton_self _)
  have hY₂ : wv t.mem (off p.x.B p.x.o) (slot p.x.wx Public.aY) p.x.wx =
      wv s.mem (off p.x.B p.x.o) (slot p.x.wx Public.aY) p.x.wx := by
    have rY := redcRanges_arr p.x.wx (j := Public.aY) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
    have := slot_le (w := p.x.wx) (show Public.aY < 8 by decide)
    have := hc.good.scr.nowrap
    exact f₂.wv_eq (fun r hr => by have := rY r hr; omega) (by omega)
  have hR : Nat.Coprime (2 ^ (64 * p.x.wx)) X := VG.Proof.Bignum.coprime_pow2 hXodd _
  obtain ⟨x, hx⟩ := VG.Proof.Bignum.exists_mont hR (by omega)
    (wv t.mem (off p.x.B p.x.o) (slot p.x.wx aXc) p.x.wx)
  obtain ⟨y, hy⟩ := VG.Proof.Bignum.exists_mont hR (by omega)
    (wv t.mem (off p.x.B p.x.o) (slot p.x.wx Public.aY) p.x.wx)
  exact ⟨mx, X, x, y, eb, hc₂, hwx2, hwx, by omega, hX₂.n, hX₂.inv, hXodd, hlt₂, hx,
    by rw [hY₂]; exact hyl, hy,
    hsd, hsln, by rw [fx₂.x_below (by omega) ho64]; exact hep, by rw [fx₂.x_below (by omega) ho64]; exact hel,
    hlen, hL1, hL2, he.congrK (InScr.of_frm fx₂ fun r hr => by
      rw [List.mem_singleton.mp hr]; simp only [xRange]; omega) k₂⟩

end CrtCTQ

open CrtCTQ in
/-- The power in a prime's phase is constant time. -/
theorem pow_ct (M : Mont) {sl sd slen : Nat} (hR : RedcCT M Public.aY) (hE : ExpCT M sd slen)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rdi (.mem (hdr sl))]) hc).isSome = true) :
    PowCT M sl sd slen := by
  unfold PowCT
  simp only [List.append_assoc]
  refine RelCT.seqs_append (by simp) (by simp [redc]) (RelCT.seq (two_piece (Ψ := P1 sd slen) [.rdi]
    (pinsRdi (fun p : BPub => p.x.B) fun _ _ ⟨_, _, _, _, _, _, hg, _⟩ => hg.rdi) hT
    fun _ _ h => blk_p1 h) ?_)
  exact RelCT.seqs_append (by simp [redc]) (by simp [Crt.expLoop]) (RelCT.seq (two_post (Ψ := EPre sd slen)
    (two_map BPub.x (fun _ _ ⟨mx, X, _, hc, hX, hwx2, hwx, hw28, hX1, _⟩ =>
      ⟨mx, X, hc, hX, hwx2, hwx, by omega, hX1, by decide⟩) hR) fun _ _ h => redc_ePre M h) hE)

namespace CrtCTQ

/-- The start of `q`'s phase's public data. -/
def up (p : PhasePub) : UPub := ⟨p.B, p.Z, p.w, p.minv, p.N, p.o, p.wx⟩

/-- The power's public data. -/
def sp (p : PhasePub) : BPub := ⟨⟨p.B, p.Z, p.o, p.w, p.wx⟩, p.ep, p.len⟩

theorem uPre {p : PhasePub} {s : State} (h : QPre p s) : UPre sWsQ (up p) s := by
  obtain ⟨mx, X, _, _, hg, hw, hw28, hlo, hhi, hwx2, hwx, hslv, hws, hN, hodd, hN1, -, hX, hX1, hXodd, -⟩ := h
  exact ⟨mx, X, hg, hw, hw28, hlo, hhi, hwx2, hwx, by decide, by decide, by decide, hslv, hws, hN, hodd, hN1,
    hX, hX1, hXodd⟩

/-- After the start of `q`'s phase. -/
def Q1 (p : PhasePub) (t : State) : Prop :=
  ∃ (mx : BitVec 64) (X : Nat) (eb : List Byte), Good t p.B p.Z p.w p.minv ∧ 8 ≤ p.w ∧ p.w < 2 ^ 28 ∧
    slot p.w 8 ≤ p.o ∧ p.o + slot p.wx 8 + tabBytes p.wx ≤ p.Z ∧ 2 ≤ p.wx ∧ p.wx ≤ p.w ∧
    word t.mem p.B (8 * sWsQ) = off p.B p.o ∧ WsAt t.mem p.B p.o p.wx mx ∧ NVals t p.B p.w p.minv p.N ∧
    wv t.mem p.B (slot p.w Public.aY) p.w < p.N ∧ XVals t p.B p.o p.wx mx X ∧ 1 < X ∧ X % 2 = 1 ∧
    wv t.mem (off p.B p.o) (slot p.wx Public.aY) p.wx < X ∧ word t.mem p.B (8 * sDq) = p.ep ∧
    word t.mem p.B (8 * sQlen) = BitVec.ofNat 64 eb.length ∧ eb.length = p.len ∧ 1 ≤ eb.length ∧
    eb.length ≤ 1024 ∧ Src t p.B p.Z p.ep eb

theorem unit_q1 (M : Mont) {p : PhasePub} {s : State} (h : QPre p s) :
    WP isa (seqs (unitSteps M.mm sWsQ)) s (Q1 p) := by
  obtain ⟨mx, X, _, eb, hg, hw, hw28, hlo, hhi, hwx2, hwx, hslv, hws, hN, hodd, hN1, -, hX, hX1, hXodd, hep,
    hel, hlen, hL1, hL2, he⟩ := h
  have hn := hg.scr.nowrap
  have h8 := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
  have hz : p.B.toNat + slot p.w 8 ≤ 2 ^ 64 := by omega
  refine WP.mono (unitPhase_ok M hg hw hw28 hlo hhi hwx2 hwx (by decide) (by decide) (by decide) hslv hws hN
    hodd hN1 hX hX1 hXodd) fun t ⟨hg₁, hws₁, hX₁, hlt₁, _, hlq₁, _, _, f₁, k₁⟩ => ?_
  have hX8 : 8 * 17 ≤ slot p.wx 8 := by unfold slot hdrBytes; omega
  exact ⟨mx, X, eb, hg₁, hw, hw28, hlo, hhi, hwx2, hwx,
    by rw [Frm.gx_hdr f₁ hlo (by decide) (by decide) (by decide)]; exact hslv, hws₁,
    hN.of_frm f₁ hlo hz (by omega), hlt₁, hX₁, hX1, hXodd, hlq₁,
    by rw [Frm.gx_hdr f₁ hlo (by decide) (by decide) (by decide)]; exact hep,
    by rw [Frm.gx_hdr f₁ hlo (by decide) (by decide) (by decide)]; exact hel, hlen, hL1, hL2,
    he.congrK (InScr.of_frm f₁ fun r hr => (gxRanges_le hlo r hr).trans hhi) k₁⟩

theorem mm_pwPre (M : Mont) {p : PhasePub} {s : State} (h : Q1 p s) :
    WP isa (M.mm Public.aY Public.aXm Public.aY) s (PwPre sWsQ sDq sQlen (sp p)) := by
  obtain ⟨mx, X, eb, hg, hw, hw28, hlo, hhi, hwx2, hwx, hslv, hws, hN, hlt, hX, hX1, hXodd, hyl, hep, hel, hlen,
    hL1, hL2, he⟩ := h
  have hn := hg.scr.nowrap
  have h8 := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot p.wx 8 := by unfold slot hdrBytes; omega
  have hoL : p.o + slot p.wx 8 ≤ 2 ^ 64 := by omega
  refine WP.mono (mmY_ok M hg (by omega) (by omega) (by omega) (a := Public.aXm) (by decide) (by decide)
    (by decide) hN hlt) fun t ⟨hg₂, _, _, f₂, k₂⟩ => ?_
  have f₂' : Frm p.B (gRanges p.w ++ [xRange p.o p.wx]) s.mem t.mem :=
    Frm.mono f₂ fun r hr => List.mem_append_left _ hr
  have hY₂ : wv t.mem (off p.B p.o) (slot p.wx Public.aY) p.wx =
      wv s.mem (off p.B p.o) (slot p.wx Public.aY) p.wx := by
    have := slot_le (w := p.wx) (show Public.aY < 8 by decide)
    rw [wv_off, wv_off]
    exact f₂.wv_eq (fun r hr => Or.inr (by have := gRanges_le p.w r hr; omega)) (by omega)
  -- `N := 1` makes the facts about the modulus trivial: the power's time does not depend on them.
  dsimp only [PwPre, sp]
  refine ⟨p.minv, mx, 1, X, 0, eb, hg₂, hw28, hlo, hhi, hwx2, hwx, by decide,
    by rw [Frm.gx_hdr f₂' hlo (by decide) (by decide) (by decide)]; exact hslv, WsAt.of_g hws f₂ hlo (by omega),
    hX.of_below f₂ (fun r hr => (gRanges_le _ r hr).trans hlo) hoL, hX1, hXodd, by simp only [Nat.mod_one],
    by rw [hY₂]; exact hyl, fun hd => absurd (Nat.le_of_dvd Nat.one_pos hd) (by omega), by decide, by decide,
    by rw [Frm.gx_hdr f₂' hlo (by decide) (by decide) (by decide)]; exact hep,
    by rw [Frm.gx_hdr f₂' hlo (by decide) (by decide) (by decide)]; exact hel, hlen, hL1, hL2,
    he.congrK (InScr.of_frm f₂' fun r hr => (gxRanges_le hlo r hr).trans hhi) k₂⟩

/-- After the power: in the prime's workspace. -/
def Q3 (p : PhasePub) (t : State) : Prop :=
  ∃ (mx : BitVec 64) (X : Nat), SubCtx t p.B p.Z p.o p.w p.wx mx ∧ XVals t p.B p.o p.wx mx X ∧ 1 < X ∧
    2 ≤ p.wx ∧ p.wx < 2 ^ 28

theorem pow_q3 (M : Mont) {p : PhasePub} {s : State} (h : PwPre sWsQ sDq sQlen (sp p) s) :
    WP isa (seqs (powSteps M.mm sWsQ sDq sQlen)) s (Q3 p) := by
  obtain ⟨_, mx, _, X, _, eb, hg, hw28, hlo, hhi, hwx2, hwx, hsl, hslv, hws, hX, hX1, hXodd, hnY, hyl, hyc, hsd,
    hsln, hep, hel, _, hL1, hL2, he⟩ := h
  exact WP.mono (powPhase_ok M hg hw28 hlo hhi hwx2 hwx hsl hslv hws hX hX1 hXodd hnY hyl hyc hsd hsln hep hel
    hL1 hL2 he) fun _ ⟨hc, hX', _⟩ => ⟨mx, X, hc, hX', hX1, hwx2, (by omega : (sp p).x.wx < 2 ^ 28)⟩

/-- Back to `Y`'s value, and to the modulus' workspace. -/
theorem mmLeave_ct (M : Mont) :
    RelCT isa (Two Q3) (seqs [M.mm Public.aY Public.aY Public.aOne, .block [leave]]) fun _ _ => True := by
  show RelCT isa _ (.seq _ _) _
  refine RelCT.seq (two_post (Ψ := fun p t => t.gpr .rdi = off p.B p.o)
    (two_map (fun p : PhasePub => (⟨off p.B p.o, slot p.wx 8, p.wx⟩ : Ws))
      (fun _ _ ⟨mx, _, hc, _⟩ => ⟨mx, hc.good, Nat.le_refl _⟩) (M.ct (by unfold MmUse; decide)))
    fun _ _ ⟨_, _, hc, hX, hX1, hwx2, hwx⟩ => WP.mono (M.mm_ok hc.good (Nat.le_refl _) hwx2 (by omega)
      (o := Public.aY) (a := Public.aY) (b := Public.aOne) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hX.inv (by rw [hX.one, hX.n]; exact hX1))
      fun _ h => h.1.rdi) ?_
  exact two_taint [.rdi] (pinsRdi (fun p : PhasePub => off p.B p.o) fun _ _ h => h) (by taint_decide)

end CrtCTQ

open CrtCTQ in
/-- `q`'s phase is constant time. -/
theorem qPhase_ct (M : Mont) (hU : UnitCT M sWsQ) (hP : PowCT M sWsQ sDq sQlen) : QPhaseCT M := by
  unfold QPhaseCT
  rw [qPhase_eq]
  refine RelCT.seqs_append (by simp [unitSteps, Crt.gPow]) (by simp) (RelCT.seq (two_post (Ψ := Q1)
    (two_map up (fun _ _ h => uPre h) hU) fun _ _ h => unit_q1 M h) ?_)
  refine RelCT.seqs_append (by simp) (by simp [powSteps]) (RelCT.seq (two_post
    (Ψ := fun p => PwPre sWsQ sDq sQlen (sp p))
    (two_map (fun p : PhasePub => (⟨p.B, p.Z, p.w⟩ : Ws))
      (fun _ _ ⟨_, _, _, hg, _, _, hlo, hhi, _⟩ =>
        ⟨_, hg, by dsimp only; omega⟩)
      (M.ct (by unfold MmUse; decide))) fun _ _ h => mm_pwPre M h) ?_)
  exact RelCT.seqs_append (by simp [powSteps]) (by simp) (RelCT.seq (two_post (Ψ := Q3)
    (two_map sp (fun _ _ h => h) hP) fun _ _ h => pow_q3 M h) (mmLeave_ct M))

end VG.Proof.Bignum.X86_64

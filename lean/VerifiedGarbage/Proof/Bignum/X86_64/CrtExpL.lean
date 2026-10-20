module

public import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp5
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSelVExp

/-!
# RSA with the CRT on x86-64: the exponentiation, as the phases need it

`Crt.code mul ex` takes its exponentiation in a prime's workspace, `ex sp sl`
for the exponent's pointer and length in `n`'s slots `sp` and `sl`: `expLoop`
by windows of 4 bits with a table of 16 entries (`CrtExpL.w4`), or
`expLoop5` by windows of 5 bits with a table of 32 read with AVX2
(`CrtExpL.w5`). A `CrtExpL` is such a code with what the phases need of
it: `Y := x^e R` in the prime's `aY`, changing only `crtExpRanges5`, within
the room for a table of 32 entries.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64

/-- An exponentiation in a prime's workspace, by the multiplication `M`:
as `crtExpLoop_ok`. -/
structure CrtExpL (M : Mont) where
  code : Nat → Nat → List (Prog isa)
  ne : ∀ sp sl, code sp sl ≠ []
  ok {s : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {X x : Nat} {Q : Prop}
    (hc : SubCtx s B Z o w wx minv) (hT : o + slot wx 8 + wsTab wx ≤ Z) (hw2 : 2 ≤ wx)
    (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hn : wv s.mem (off B o) (slot wx aN) wx = X)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hodd : X % 2 = 1)
    (hxl : wv s.mem (off B o) (slot wx Crt.aXc) wx < X)
    (hxc : Q → wv s.mem (off B o) (slot wx Crt.aXc) wx % X = x * 2 ^ (64 * wx) % X)
    (hyl : wv s.mem (off B o) (slot wx aY) wx < X)
    (hyc : Q → wv s.mem (off B o) (slot wx aY) wx % X = 2 ^ (64 * wx) % X)
    {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) {ep : Addr} {eb : List Byte}
    (hep : word s.mem B (8 * sp) = ep) (hel : word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length)
    (hL1 : 1 ≤ eb.length) (hL2 : eb.length ≤ 1024) (he : Src s B Z ep eb) :
    WP isa (seqs (code sp sl)) s fun t => SubCtx t B Z o w wx minv ∧
      wv t.mem (off B o) (slot wx aY) wx < X ∧
      (Q → wv t.mem (off B o) (slot wx aY) wx % X = x ^ Spec.Rsa.os2ip eb * 2 ^ (64 * wx) % X) ∧
      Frm (off B o) (crtExpRanges5 wx) s.mem t.mem ∧ Keep mmRegs s t

/-- `expLoop`'s ranges are within `expLoop5`'s. -/
theorem crtExpRanges_widen5 (wx : Nat) :
    ∀ r ∈ crtExpRanges wx, ∃ r' ∈ crtExpRanges5 wx, r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 := by
  intro r hr
  simp only [crtExpRanges, List.mem_cons] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | hr
  · exact ⟨_, by simp [crtExpRanges5, crtExpRanges], Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨_, by simp [crtExpRanges5, crtExpRanges], Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨_, by simp [crtExpRanges5, crtExpRanges], Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨_, by simp [crtExpRanges5, crtExpRanges], Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨(slot wx 8, tabBytes wx 32), by simp [crtExpRanges5, crtExpRanges], Nat.le_refl _,
      by unfold tabBytes; omega⟩
  · exact ⟨r, crtExpRanges_sub5 wx r (crtWinRanges_sub wx r hr), Nat.le_refl _, Nat.le_refl _⟩

/-- `expLoop` by windows of 4 bits, its table of 16 read with SSE2. -/
def CrtExpL.w4 (M : Mont) : CrtExpL M where
  code := Crt.expLoop M.mm Crt.tabSelect
  ne _ _ := by simp [Crt.expLoop, Crt.expLoopS]
  ok hc _ hw2 hwx hw30 hn hinv hodd hxl hxc hyl hyc _ _ hsp hsl _ _ hep hel hL1 hL2 he :=
    WP.mono (crtExpLoop_ok M CrtSel.sse hc hw2 hwx hw30 hn hinv hodd hxl hxc hyl hyc hsp hsl hep hel hL1 hL2 he)
      fun _ ⟨h1, h2, h3, f, k⟩ => ⟨h1, h2, h3, f.widen (crtExpRanges_widen5 _), k⟩

/-- `expLoop5` by windows of 5 bits, its table of 32 read with AVX2. -/
def CrtExpL.w5 (M : Mont) : CrtExpL M where
  code := Crt.expLoop5 M.mm Crt.tabSelectV
  ne _ _ := by simp [Crt.expLoop5, Crt.expLoop5S]
  ok hc hT hw2 hwx hw30 hn hinv hodd hxl hxc hyl hyc _ _ hsp hsl _ _ hep hel hL1 hL2 he :=
    crtExpLoop5_ok M CrtSel.avx hc hT hw2 hwx hw30 hn hinv hodd hxl hxc hyl hyc hsp hsl hep hel hL1 hL2 he

/-- `CrtExpL.w4` with its squarings by `Sq`. -/
def CrtExpL.w4S (M : Mont) (Sq : MontS) : CrtExpL M where
  code := Crt.expLoopS Sq.mm M.mm Crt.tabSelect
  ne _ _ := by simp [Crt.expLoopS]
  ok hc _ hw2 hwx hw30 hn hinv hodd hxl hxc hyl hyc _ _ hsp hsl _ _ hep hel hL1 hL2 he :=
    WP.mono (crtExpLoopS_ok M Sq CrtSel.sse hc hw2 hwx hw30 hn hinv hodd hxl hxc hyl hyc hsp hsl hep hel hL1 hL2 he)
      fun _ ⟨h1, h2, h3, f, k⟩ => ⟨h1, h2, h3, f.widen (crtExpRanges_widen5 _), k⟩

/-- `CrtExpL.w5` with its squarings by `Sq`. -/
def CrtExpL.w5S (M : Mont) (Sq : MontS) : CrtExpL M where
  code := Crt.expLoop5S Sq.mm M.mm Crt.tabSelectV
  ne _ _ := by simp [Crt.expLoop5S]
  ok hc hT hw2 hwx hw30 hn hinv hodd hxl hxc hyl hyc _ _ hsp hsl _ _ hep hel hL1 hL2 he :=
    crtExpLoop5S_ok M Sq CrtSel.avx hc hT hw2 hwx hw30 hn hinv hodd hxl hxc hyl hyc hsp hsl hep hel hL1 hL2 he

end VG.Proof.Bignum.X86_64

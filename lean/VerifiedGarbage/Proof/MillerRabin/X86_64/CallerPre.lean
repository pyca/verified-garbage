module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSq
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rsa.Ranges
public import VerifiedGarbage.Proof.MillerRabin.Contract
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnVerified

/-! ### `MillerRabin.X86_64.Prepared`, which this module and modules that import it used -/

section

/-! # Existing Montgomery contexts satisfy the callable's prepared contract -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaKeyGen VG.Proof.RsaKeyGen.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum.X86_64.MontFn (numAt_eq)

theorem ctx_width {s : State} {B : Addr} {Z w c bm : Nat} {mi : BitVec 64} (hc : MrCtx s B Z w mi c bm) (h128 : w ≤ 128) :
    Proof.Rsa.Mont.wOf s.mem B = w := by
  change (word s.mem B (8 * sW)).toNat = w
  rw [hc.good.hdr.hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]

theorem prepared_of_ctx {s : State} {B : Addr} {Z w c bm : Nat} {mi : BitVec 64}
    (hc : MrCtx s B Z w mi c bm) (he : ECtx s.mem B w c) (h128 : w ≤ 128)
    (ho : c % 2 = 1) (h3 : 3 ≤ c) (hx : wv s.mem B (slot w aXm) w < c) :
    Proof.MillerRabin.Round.Prepared Proof.MillerRabin.Round.extended s.mem B := by
  have hw := ctx_width hc h128
  have hn : Proof.Rsa.Mont.numAt s.mem B w 0 = c := (numAt_eq s.mem B w 0).trans hc.n
  simp only [Proof.MillerRabin.Round.Prepared, hw, hn, Proof.MillerRabin.Round.extended]
  refine ⟨h3, ho, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ((word s.mem B (slot w aN)).toNat * (word s.mem B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0
    rw [hc.good.hdr.hminv]
    exact hc.inv
  · rw [numAt_eq]
    exact hx
  · rw [numAt_eq]
    exact hc.r1
  · rw [numAt_eq]
    exact hc.rm1
  · rw [numAt_eq]
    simpa only [Proof.MillerRabin.Round.exponent, Proof.MillerRabin.Round.shift, mrE, mrSig, sigOf, mrA, aE] using he.e
  · exact he.l

theorem layout_of_ctx {s : State} {B : Addr} {Z w c bm : Nat} {mi : BitVec 64}
    (hc : MrCtx s B Z w mi c bm) (h4 : 4 ≤ w) (h128 : w ≤ 128) :
    Proof.MillerRabin.Round.Layout Proof.MillerRabin.Round.extended s.mem B (32 + 28 * (w + 2)) := by
  simp only [Proof.MillerRabin.Round.Layout, ctx_width hc h128, Proof.MillerRabin.Round.extended,
    Proof.Rsa.Mont.Layout, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
  refine ⟨Or.inl trivial, ⟨by omega_arith, by omega_arith, by omega_arith, ?_⟩,
    h4, h128, ?_, True.intro⟩
  · intro j hj
    exact hc.good.hdr.harr j hj
  · change 256 + 27 * (8 * (w + 2)) ≤ 8 * (32 + 28 * (w + 2))
    omega_arith

end VG.Proof.MillerRabin.X86_64

end

end

/-! ### `MillerRabin.X86_64.CallerEntry`, which this module and modules that import it used -/

section

/-! # A shared call's return address preserves the prepared workspace -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64.Caller

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate

theorem entry_frame (s : State) : Frame [below (s.gpr .rsp) 8] s.mem s.callEntry.mem := by
  rw [State.callEntry_mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))

theorem entry_byte (s : State) {B : Addr} {Z i : Nat}
    (hn : B.toNat + Z ≤ 2 ^ 64) (hi : i < Z)
    (hs : Region.Disjoint ⟨B, Z⟩ (below (s.gpr .rsp) 128)) :
    s.callEntry.mem (off B i) = s.mem (off B i) := by
  apply (entry_frame s).bytes (R := ⟨B, Z⟩) ?_ (by change Z ≤ 2 ^ 64; omega_arith) hi
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact hs.sub_right (below_sub (by decide) (by decide))

theorem entry_word (s : State) {B : Addr} {Z d : Nat}
    (hn : B.toNat + Z ≤ 2 ^ 64) (hd : d + 8 ≤ Z)
    (hs : Region.Disjoint ⟨B, Z⟩ (below (s.gpr .rsp) 128)) :
    word s.callEntry.mem B d = word s.mem B d := by
  have hf := entry_frame s
  apply hf.readW (r := ⟨B, Z⟩)
    (Offset.contains_base B hd (by omega_arith)) ?_ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact hs.sub_right (below_sub (by decide) (by decide))

theorem entry_wv (s : State) {B : Addr} {Z d k : Nat}
    (hn : B.toNat + Z ≤ 2 ^ 64) (hd : d + 8 * k ≤ Z)
    (hs : Region.Disjoint ⟨B, Z⟩ (below (s.gpr .rsp) 128)) :
    wv s.callEntry.mem B d k = wv s.mem B d k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [wv, wv, ih (by omega_arith), entry_word s hn (by omega_arith) hs]

theorem entry_context {s : State} {B : Addr} {Z w c bm : Nat} {mi : BitVec 64}
    (hc : MrCtx s B Z w mi c bm) (he : ECtx s.mem B w c) (hd : MrDims B Z w)
    (hs : Region.Disjoint ⟨B, Z⟩ (below (s.gpr .rsp) 128)) :
    MrCtx s.callEntry B Z w mi c bm ∧ ECtx s.callEntry.mem B w c := by
  have hn := hc.good.scr.nowrap
  have hz := hd.x
  have hHdr : ∀ i < 16, word s.callEntry.mem B (8 * i) = word s.mem B (8 * i) :=
    fun i hi => entry_word s hn (by
      have := hdr_lt_slot w 8 (by omega_arith : i < 32)
      have := hd.z
      omega_arith) hs
  have hArr : ∀ j < 27, wv s.callEntry.mem B (slot w j) w = wv s.mem B (slot w j) w :=
    fun j hj => entry_wv s hn (by
      have hslot := VG.Proof.Rsa.slot_lt (w := w) hj
      simp only [slot, hdrBytes, aRm1] at hz hslot ⊢
      omega_arith) hs
  refine ⟨⟨⟨hc.good.scr.congr rfl, by
      rw [State.callEntry_gpr _ (by decide)]; exact hc.good.rdi,
      ⟨(hHdr sW (by decide)).trans hc.good.hdr.hw,
        (hHdr sMinv (by decide)).trans hc.good.hdr.hminv,
        fun j hj => (hHdr (sArr j) (by unfold sArr; omega_arith)).trans (hc.good.hdr.harr j hj)⟩⟩,
    ?_, (hArr aN (by decide)).trans hc.n, (hArr aB (by decide)).trans hc.b,
    (hArr aR1 (by decide)).trans hc.r1, (hArr aRm1 (by decide)).trans hc.rm1⟩, ?_⟩
  · rw [entry_word s hn (by
      have := hd.w4
      simp only [slot, hdrBytes, aRm1, aN] at hz ⊢
      omega_arith) hs]
    exact hc.inv
  · refine ⟨(hArr aE (by decide)).trans he.e, ?_⟩
    rw [entry_word s hn (by
      simp only [slot, hdrBytes, aRm1, aE] at hz ⊢
      omega_arith) hs]
    exact he.l

end VG.Proof.MillerRabin.X86_64.Caller

end

end

/-! # The caller provides the shared round's workspace and stack -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64.Caller

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate

def callWords (w : Nat) : Nat := 32 + 28 * (w + 2)

def narrowed (s : State) (B : Addr) (w : Nat) : State :=
  s.callEntry.withRegions [] [⟨B, 8 * callWords w⟩]

structure Room (s : State) (B : Addr) (Z : Nat) : Prop where
  size : 128 ≤ (s.gpr .rsp).toNat
  disjoint : Region.Disjoint ⟨B, Z⟩ (below (s.gpr .rsp) 128)

theorem call_size {w Z : Nat} (hZ : slot w 28 ≤ Z) : 8 * callWords w ≤ Z := by
  simp only [callWords, slot, hdrBytes] at hZ ⊢
  omega_arith

theorem narrow_pre {s : State} {B : Addr} {Z w c bm : Nat} {mi : BitVec 64}
    (hc : MrCtx s B Z w mi c bm) (he : ECtx s.mem B w c) (hd : MrDims B Z w)
    (hZ : slot w 28 ≤ Z) (hr : Room s B Z)
    (hsi : s.gpr .rsi = BitVec.ofNat 64 (callWords w))
    (ho : c % 2 = 1) (h3 : 3 ≤ c) (hx : wv s.mem B (slot w aXm) w < c) :
    roundPre (narrowed s B w) := by
  have hn := hc.good.scr.nowrap
  have hsize := call_size hZ
  have hw := hd.w128
  have hN : callWords w < 2 ^ 64 := by unfold callWords; omega_arith
  obtain ⟨hce, hee⟩ := entry_context hc he hd hr.disjoint
  have heX : wv s.callEntry.mem B (slot w aXm) w < c := by
    rw [entry_wv s hn (by
      have hz := hd.x
      simp only [slot, hdrBytes, aRm1, aXm] at hz ⊢
      omega_arith) hr.disjoint]
    exact hx
  have hSub : Region.Sub ⟨B, 8 * callWords w⟩ ⟨B, Z⟩ := by
    intro x hx
    simp only [Region.Contains] at hx ⊢
    omega_arith
  have hD := (hr.disjoint.sub_left hSub).symm
  dsimp only [roundPre, narrowed, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_mem]
  rw [State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), hc.good.rdi,
    State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp), hsi,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN]
  simp only [Nat.mul_comm (callWords w) 8]
  refine ⟨trivial, trivial, by omega_arith, ?_, ?_, ?_,
    layout_of_ctx hce hd.w4 hd.w128, prepared_of_ctx hce hee hd.w128 ho h3 heX⟩
  · rw [State.callEntry_rsp]
    change 120 ≤ (s.gpr .rsp - BitVec.ofNat 64 8).toNat
    rw [toNat_sub_ofNat (k := 8) (by have := hr.size; omega_arith)]
    have := hr.size
    omega_arith
  · rw [State.callEntry_rsp]
    change Region.Disjoint (below (s.gpr .rsp) 8) ⟨B, 8 * callWords w⟩
    exact hD.sub_left (below_sub (sp := s.gpr .rsp) (a := 8) (b := 128) (by decide) (by decide))
  · rw [State.callEntry_rsp]
    change Region.Disjoint (below (s.gpr .rsp - 8#64) 120) ⟨B, 8 * callWords w⟩
    exact hD.sub_left (below_callee (s.gpr .rsp) 120)

theorem narrow_covers {s : State} {B : Addr} {Z w : Nat} (h : Scr s B Z) (hZ : slot w 28 ≤ Z) :
    Covers ([] ++ [⟨B, 8 * callWords w⟩]) (s.rd ++ s.wr) ∧
      Covers [⟨B, 8 * callWords w⟩] s.wr := by
  have hreg : InRegions s.wr B (8 * callWords w) := by
    simpa only [InRegions, off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] using
      h.region (d := 0) (n := 8 * callWords w) (by have := call_size hZ; omega_arith)
        (by unfold callWords; omega_arith)
  refine ⟨Covers.one ?_, Covers.one hreg⟩
  obtain ⟨r, hm, hc⟩ := hreg
  exact ⟨r, List.mem_append_right _ hm, hc⟩

end VG.Proof.MillerRabin.X86_64.Caller

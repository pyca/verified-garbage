module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Arguments
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops

/-! # Exact values and memory effects of native argument transfers -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Bignum.AArch64 VG.Impl.Dsa.AArch64.Generation
open VG.Proof.Rsa.AArch64

def argumentValue (W : Nat → BitVec 64) : ArgumentValue → BitVec 64
  | .ones => BitVec.allOnes 64
  | .literal n => BitVec.ofNat 64 n
  | .frame k offset => W k + BitVec.ofNat 64 offset

def argumentFits (a : HeaderArgument) : Prop :=
  16 ≤ a.destination ∧ a.destination < 32 ∧
    match a.value with
    | .ones => True
    | .literal n => n < 2 ^ 16
    | .frame k offset => k < 34 ∧ offset < 2 ^ 16

def argumentWrites (B : Addr) (W : Nat → BitVec 64) : Mem → List HeaderArgument → Mem
  | m, [] => m
  | m, a :: rest => argumentWrites B W (m.writeW (off B (8 * a.destination)) (argumentValue W a.value)) rest

theorem headerArgument_ok {s : State} {B F : Addr} {W : Nat → BitVec 64}
    (a : HeaderArgument) (ha : argumentFits a) (hB : Scr s B 256)
    (hdi : s.gpr .x0 = B) (hsp : s.sp = F)
    (hr : ∀ k < 34, InRegions (s.rd ++ s.wr) (off F (8 * k)) 8)
    (hwords : ∀ k < 34, word s.mem F (8 * k) = W k) :
    WP isa (.block (headerArgument a)) s fun t =>
      t.mem = s.mem.writeW (off B (8 * a.destination)) (argumentValue W a.value) ∧ Keep [.x3, .x4] s t := by
  have hd := ha.1
  have hd' := ha.2.1
  have hv := ha.2.2
  refine WP.keep [.x3, .x4] ?_ (by rcases a with ⟨d, v⟩; cases v <;> rfl)
    (by rcases a with ⟨d, v⟩; cases v <;> rfl) (by rcases a with ⟨d, v⟩; cases v <;> rfl)
  cases he : a.value with
  | ones =>
    brun [headerArgument, he, hdi, hdr_enc hd', hB.st (d := 8 * a.destination) (by omega)]
    rfl
  | literal n =>
    rw [he] at hv
    brun [headerArgument, he, hdi, hdr_enc hd', hB.st (d := 8 * a.destination) (by omega), argumentValue, off]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)]
  | frame k offset =>
    rw [he] at hv
    have henc : 8 * k % 8 = 0 ∧ 8 * k < 32768 := by omega
    brun [headerArgument, he, exec_ldrSp henc, hsp, hdi, hdr_enc hd',
      hB.st (d := 8 * a.destination) (by omega), hr k hv.1, hwords k hv.1]
    congr 2
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hv.2, Nat.mod_eq_of_lt (by omega : offset < 2 ^ 64)]

/-- A whole argument table preserves its stack sources across every write. -/
theorem headerArguments_ok {s : State} {B F : Addr} {W : Nat → BitVec 64}
    (args : List HeaderArgument) (ha : ∀ a ∈ args, argumentFits a)
    (hB : Scr s B 256) (hdi : s.gpr .x0 = B) (hsp : s.sp = F)
    (hr : ∀ k < 34, InRegions (s.rd ++ s.wr) (off F (8 * k)) 8)
    (hwords : ∀ k < 34, word s.mem F (8 * k) = W k)
    (hsep : ∀ k < 34, ∀ j < 32, Mem.Sep (off F (8 * k)) 8 (off B (8 * j)) 8) :
    WP isa (.block (headerArguments args)) s fun t =>
      t.mem = argumentWrites B W s.mem args ∧ Keep [.x3, .x4] s t := by
  induction args generalizing s with
  | nil => exact WP.block_nil ⟨rfl, Keep.refl _ _⟩
  | cons a rest ih =>
    change WP isa (.block (headerArgument a ++ headerArguments rest)) s _
    rw [WP.block_append_iff]
    have haa := ha a (by simp)
    refine WP.mono (headerArgument_ok a haa hB hdi hsp hr hwords) fun u ⟨hm, hk⟩ => ?_
    refine WP.mono (ih (fun b hb => ha b (List.mem_cons_of_mem _ hb)) (hB.congr hk.wr)
      ((hk.gpr _ (by decide)).trans hdi) (hk.sp.trans hsp)
      (fun k h => by rw [hk.rd, hk.wr]; exact hr k h)
      (fun k h => by
        rw [hm]
        change (s.mem.writeW (off B (8 * a.destination)) _).readW (off F (8 * k)) 64 = _
        rw [Mem.readW_writeW_sep (hsep k h a.destination haa.2.1) (by decide)]
        exact hwords k h)) fun t ⟨htm, kt⟩ => ?_
    exact ⟨by rw [htm, hm]; rfl, (hk.trans kt).mono (by decide)⟩

/-- Argument stores touch only the operation-specific half of the header. -/
theorem argumentWrites_outside (B : Addr) (W : Nat → BitVec 64) (m : Mem)
    (args : List HeaderArgument) (ha : ∀ a ∈ args, argumentFits a) :
    Outside B 128 128 m (argumentWrites B W m args) := by
  induction args generalizing m with
  | nil => exact Outside.refl _ _ _ _
  | cons a rest ih =>
    have h := ha a (by simp)
    have hd := h.1
    have hd' := h.2.1
    have hf : Outside B 128 128 m (m.writeW (off B (8 * a.destination)) (argumentValue W a.value)) :=
      (writeW_outside _ _ _ (by omega)).mono (by omega) (by omega)
    exact hf.trans (ih _ (fun b hb => ha b (List.mem_cons_of_mem _ hb)))

def argumentWords (W H : Nat → BitVec 64) : List HeaderArgument → Nat → BitVec 64
  | [] => H
  | a :: rest => argumentWords W (fun k => if k = a.destination then argumentValue W a.value else H k) rest

theorem argumentWords_congr (W : Nat → BitVec 64) (args : List HeaderArgument)
    {H H' : Nat → BitVec 64} (he : ∀ j < 32, H j = H' j) {k : Nat} (hk : k < 32) :
    argumentWords W H args k = argumentWords W H' args k := by
  induction args generalizing H H' with
  | nil => exact he k hk
  | cons a rest ih =>
    apply ih
    intro j hj
    by_cases hjd : j = a.destination <;> simp only [hjd, ite_true, ite_false]
    exact he j hj

/-- Evaluate header words independently of the underlying byte stores. -/
theorem argumentWrites_word (B : Addr) (W : Nat → BitVec 64) (m : Mem)
    (args : List HeaderArgument) (ha : ∀ a ∈ args, argumentFits a) {k : Nat} (hk : k < 32) :
    word (argumentWrites B W m args) B (8 * k) = argumentWords W (fun j => word m B (8 * j)) args k := by
  induction args generalizing m with
  | nil => rfl
  | cons a rest ih =>
    have h := ha a (by simp)
    rw [argumentWrites, ih _ (fun b hb => ha b (List.mem_cons_of_mem _ hb))]
    apply argumentWords_congr W rest (k := k) _ hk
    intro j hj
    by_cases hjd : j = a.destination
    · subst j
      rw [word_writeW_self, ite_eq_left rfl]
    · rw [ite_eq_right hjd]
      exact hdrStore_hdr _ _ _ h.2.1 hj (Ne.symm hjd)

end VG.Proof.Dsa.AArch64.Generation

module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedFrame
public import VerifiedGarbage.Impl.RsaKeyGen.X86_64.SharedCandidate
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.KMain
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrShift
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdE
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages
public import VerifiedGarbage.Spec.RsaKeyGen
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrMain
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrRoundAll
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.X86_64.Template

/-! ### `RsaKeyGen.X86_64.SharedKMain`, which the modules that import this one used -/

section

/-! ### `RsaKeyGen.X86_64.SharedMain`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86_64.SharedMid`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86_64.SharedCall`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86_64.SharedWitness`, which only this module used -/

section

/-!
# A candidate on x86-64: one round of Miller–Rabin

Prepare the witness in Montgomery form for the callable shared round.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

def witnessRanges (w : Nat) : List (Nat × Nat) :=
  witRanges w ++ [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aXm, 8 * (w + 2))]

/-- Load RSA's next witness and convert it to Montgomery form. -/
theorem sharedWitness_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm : Nat}
    (hd : MrDims B Z w) (hc : MrCtx s B Z w mi c bm)
    (hR2 : wv s.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c) (hodd : c % 2 = 1) (hc1 : 1 < c)
    (hb : Spec.RsaKeyGen.bitLength (c - 1) = 64 * w)
    {rp : Addr} {used : Nat} {r : List Byte} (hR : word s.mem B (8 * kRand) = rp)
    (hU : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hsrc : Src s B Z rp r) (hlen : used + 8 * w ≤ r.length) :
    WP isa (seqs (mrWitness ++ [M.mm aXm aX aR2])) s fun t =>
      MrCtx t B Z w mi c bm ∧
      wv t.mem B (slot w aXm) w = (wtOf c w used r).1 % c * 2 ^ (64 * w) % c ∧
      wv t.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c ∧
      word t.mem B (8 * kU) =
        mask (Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w)))).2 ∧
      word t.mem B (8 * kUsed) = BitVec.ofNat 64 (used + 8 * w) ∧
      Frm B (witnessRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hg := hc.good
  have hZ := hd.z
  have hXZ := hd.x
  have hw4 := hd.w4
  have hw' : w < 2 ^ 31 := by have := hd.w128; omega_using [this]
  have hn := hg.scr.nowrap
  have hRc : Nat.Coprime (2 ^ (64 * w)) c := VG.Proof.Bignum.coprime_pow2 hodd _
  have hc0 : 0 < c := by omega_using [hc1]
  refine wp_seqs_append (by simp [mrWitness]) (by simp) ?_
  refine WP.mono (mrWitness_ok hd hc hodd hb hR hU hK (VG.Proof.RsaKeyGen.X86_64.Src.seg hsrc hlen) (by
    simp only [VG.Proof.RsaKeyGen.seg, List.length_take, List.length_drop]; omega_using [hlen]))
    fun s₁ ⟨hc₁, hx₁, hu₁, hus₁, hf₁, k₁⟩ => ?_
  dsimp only [wtOf]
  generalize hwt : Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w))) = wt
    at hx₁ hu₁ ⊢
  have hR2₁ : wv s₁.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c := by
    rw [hf₁.wv_eq (d := slot w aR2) (k := w) (by simp only [witRanges]; rng_disj)
      (by have := slot_le (w := w) (show aR2 < 8 by decide); omega_using [hZ, hn, this])]; exact hR2
  -- `b R mod c` into `aXm`.
  simp only [seqs]
  refine WP.mono (M.mm_ok hc₁.good hZ (by omega_using [hw4]) hw' (o := aXm) (a := aX) (b := aR2) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hc₁.inv
    (by rw [hR2₁, hc₁.n]; exact Nat.mod_lt _ hc0)) fun s₂ ⟨hg₂, hlt₂, hy₂, ha₂, k₂⟩ => ?_
  rw [hc₁.n] at hlt₂ hy₂
  rw [hx₁, hR2₁] at hy₂
  have hXm : wv s₂.mem B (slot w aXm) w = Spec.Rsa.powMod wt.1 1 c * 2 ^ (64 * w) % c := by
    rw [← Nat.mod_eq_of_lt hlt₂, VG.Proof.Bignum.powMod_eq, Nat.pow_one, Nat.mod_mul_mod]
    refine VG.Proof.Bignum.mont_cancel hRc ?_
    rw [hy₂, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc]
  have hf₂ : Frm B [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aXm, 8 * (w + 2))] s₁.mem s₂.mem :=
    Frm.of_arrays ha₂ (by simp)
  have hc₂ : MrCtx s₂ B Z w mi c bm := hc₁.of_frm hd hf₂ hg₂.scr hg₂.rdi (by rng_disj) (by rng_disj) (by rng_disj)
    (by rng_disj) (by rng_disj)
  have hf : Frm B (witnessRanges w) s.mem s₂.mem :=
    (hf₁.mono (fun r hr => List.mem_append_left _ hr)).trans
      (hf₂.mono (fun r hr => List.mem_append_right _ hr))
  refine ⟨hc₂, ?_, ?_, ?_, ?_, hf, (k₁.trans k₂).mono (by decide)⟩
  · simpa only [VG.Proof.Bignum.powMod_eq, Nat.pow_one] using hXm
  · rw [hf₂.wv_eq (d := slot w aR2) (k := w) (by rng_disj)
      (by have := slot_le (w := w) (show aR2 < 8 by decide); omega_arith)]
    exact hR2₁
  · rw [hf₂.word_eq (d := 8 * kU) (by rng_disj) (by unfold kU sFn; omega_arith)]
    exact hu₁
  · rw [hf₂.word_eq (d := 8 * kUsed) (by rng_disj) (by unfold kUsed sFn; omega_arith)]
    exact hus₁

end VG.Proof.RsaKeyGen.X86_64

end

end


/-!
# The candidate's Montgomery multiplications as calls

The candidate multiplies by `mm`, calls that inline to the backend's
`M.mm` (`MmCalls`). A piece of it that calls only `mm` runs as its inline
form does but for the return address, which a call stores in the 8 bytes
below `rsp` (`hole`, within the 128 the round's call uses: `SharedEnv`).
These bytes are off the working space, so what the inline run proves of
the working space holds after the calls, with `SharedFrame` for `Frm`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.MillerRabin.X86_64
open VG.Proof.MlKem.X86_64

/-- `mm` calls functions that inline to `M.mm`. -/
structure MmCalls (M : Mont) (mm : Nat → Nat → Nat → Prog isa) : Prop where
  ok : ∀ o a b, (mm o a b).InlineOk = true
  inline : ∀ o a b, (mm o a b).inline = M.mm o a b

theorem hole_below (sp : Addr) : Region.Sub (hole sp) (below sp 128) :=
  below_sub (sp := sp) (a := 8) (b := 128) (by decide) (by decide)

theorem SharedEnv.hole_clear {B sp : Addr} {Z : Nat} {s : State} (he : SharedEnv B Z sp s) :
    Clear (hole (s.gpr .rsp)) s := by
  rw [he.rsp]
  exact fun r hr => (he.clear r hr).sub_right (hole_below sp)

theorem SharedEnv.hole_miss {B sp : Addr} {Z : Nat} {s : State} (he : SharedEnv B Z sp s) {x : Addr}
    (hx : ofs B x < Z) : ¬ (hole sp).Contains x 1 := by
  intro hc
  have hd := he.room.disjoint
  rw [he.rsp] at hd
  exact hd x hx (hole_below sp x hc)

/-- The patched state agrees with the inline one on the working space. -/
theorem SharedEnv.patch_frm {B sp : Addr} {Z : Nat} {s b : State} {hv : Mem} {u : Nat → BitVec 64}
    (he : SharedEnv B Z sp s) : Frm B [(Z, 2 ^ 64)] b.mem (b.patch (hole sp) hv u).mem := by
  intro x hx
  have hx := hx _ (List.mem_singleton_self _)
  have hlt : ofs B x < 2 ^ 64 := BitVec.isLt _
  exact State.patch_mem (he.hole_miss (by omega_using [hx, hlt]))

/-- What the inline run changes, the run with calls changes, but for the
return address. -/
theorem Frm.patch_shared {B sp : Addr} {rs : List (Nat × Nat)} {m : Mem} {b : State} {hv : Mem}
    {u : Nat → BitVec 64} (hf : Frm B rs m b.mem) :
    SharedFrame B sp rs m (b.patch (hole sp) hv u).mem := by
  intro x hx hr
  rw [State.patch_mem fun hc => hx _ (List.mem_singleton_self _) (hole_below sp x hc)]
  exact hf x hr

theorem SharedEnv.patch_good {B sp : Addr} {Z w : Nat} {mi : BitVec 64} {s b : State} {hv : Mem}
    {u : Nat → BitVec 64} (he : SharedEnv B Z sp s) (hg : Good b B Z w mi) (hZ : 128 ≤ Z) :
    Good (b.patch (hole sp) hv u) B Z w mi :=
  ⟨hg.scr.congr rfl, hg.rdi, Hdr.of_frm hg.hdr he.patch_frm fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hZ⟩

theorem SharedEnv.patch_wv {B sp : Addr} {Z d k : Nat} {s b : State} {hv : Mem}
    {u : Nat → BitVec 64} (he : SharedEnv B Z sp s) (hd : d + 8 * k ≤ Z) (hn : B.toNat + Z ≤ 2 ^ 64) :
    wv (b.patch (hole sp) hv u).mem B d k = wv b.mem B d k :=
  he.patch_frm.wv_eq (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact Or.inl hd)
    (by omega_using [hd, hn])

theorem SharedEnv.patch_word {B sp : Addr} {Z d : Nat} {s b : State} {hv : Mem}
    {u : Nat → BitVec 64} (he : SharedEnv B Z sp s) (hd : d + 8 ≤ Z) (hn : B.toNat + Z ≤ 2 ^ 64) :
    word (b.patch (hole sp) hv u).mem B d = word b.mem B d :=
  he.patch_frm.word_eq (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact Or.inl hd)
    (by omega_using [hd, hn])

theorem SharedEnv.patch_mrCtx {B sp : Addr} {Z w : Nat} {mi : BitVec 64} {c bm : Nat} {s b : State}
    {hv : Mem} {u : Nat → BitVec 64} (he : SharedEnv B Z sp s) (hc : MrCtx b B Z w mi c bm)
    (hd : MrDims B Z w) : MrCtx (b.patch (hole sp) hv u) B Z w mi c bm := by
  have hx := hd.x
  have h128 : 128 ≤ Z := by
    have := slot_le (w := w) (show aN < 8 by decide)
    unfold slot aN hdrBytes at *; omega_arith
  have hsep : ∀ j, j ≤ aRm1 → ∀ r ∈ [(Z, 2 ^ 64)], slot w j + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w j := by
    intro j hj r hr
    simp only [List.mem_singleton] at hr
    subst hr
    have : slot w j ≤ slot w aRm1 := by
      unfold slot; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hj) _
    exact Or.inl (by omega_using [hx, this])
  exact MrCtx.of_frm hc hd he.patch_frm (hc.good.scr.congr rfl) hc.good.rdi
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h128)
    (hsep aN (by decide)) (hsep aB (by decide)) (hsep aR1 (by decide)) (hsep aRm1 (by decide))

/-! ## The pieces that multiply -/

theorem montSetup_inlineOk {mm : Nat → Nat → Nat → Prog isa} (hm : ∀ o a b, (mm o a b).InlineOk = true) :
    (seqs (montSetup mm)).InlineOk = true := by
  rw [inlineOk_seqs]
  unfold montSetup
  simp only [List.all_cons, List.all_nil, hm, Bool.true_and, Bool.and_true]
  decide +kernel

theorem montSetup_inline (mm : Nat → Nat → Nat → Prog isa) :
    (seqs (montSetup mm)).inline = seqs (montSetup fun o a b => (mm o a b).inline) := by
  unfold montSetup
  simp only [inline_seqs, List.map_cons, List.map_nil]
  simp (disch := decide) only [inline_of_noCalls]

theorem witness_inlineOk {mm : Nat → Nat → Nat → Prog isa} (hm : ∀ o a b, (mm o a b).InlineOk = true) :
    (seqs (mrWitness ++ [mm aXm aX aR2])).InlineOk = true := by
  rw [inlineOk_seqs, List.all_append, List.all_cons, List.all_nil, hm, Bool.true_and, Bool.and_true]
  decide +kernel

theorem witness_inline (mm : Nat → Nat → Nat → Prog isa) :
    (seqs (mrWitness ++ [mm aXm aX aR2])).inline = seqs (mrWitness ++ [(mm aXm aX aR2).inline]) := by
  simp only [inline_seqs, List.map_append, List.map_cons, List.map_nil]
  simp (disch := decide) only [map_inline_of_noCalls]

theorem MmCalls.montSetup {M : Mont} {mm : Nat → Nat → Nat → Prog isa} (hm : MmCalls M mm) :
    (seqs (montSetup mm)).inline = seqs (montSetup M.mm) := by
  rw [montSetup_inline]
  congr 2
  funext o a b
  exact hm.inline o a b

theorem MmCalls.witness {M : Mont} {mm : Nat → Nat → Nat → Prog isa} (hm : MmCalls M mm) :
    (seqs (mrWitness ++ [mm aXm aX aR2])).inline = seqs (mrWitness ++ [M.mm aXm aX aR2]) := by
  rw [witness_inline, hm.inline]

/-- `montSetup_ok`, with calls. -/
theorem montSetup_call_ok (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hm : MmCalls M mm)
    {s : State} {B sp : Addr} {Z w : Nat} {mi : BitVec 64} {N : Nat} (henv : SharedEnv B Z sp s)
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z) (hXZ : slot w aRm1 + 8 * (w + 2) ≤ Z) (hw : 4 ≤ w) (hw64 : w ≤ 64)
    (hn : wv s.mem B (slot w aN) w = N) (hodd : N % 2 = 1) (htop : 2 ^ (64 * w - 1) ≤ N) :
    WP isa (seqs (montSetup mm)) s fun t => ∃ mi' : BitVec 64, Good t B Z w mi' ∧
      ((word t.mem B (slot w aN)).toNat * mi'.toNat + 1) % 2 ^ 64 = 0 ∧
      wv t.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % N ∧
      wv t.mem B (slot w aR1) w = 2 ^ (64 * w) % N ∧
      wv t.mem B (slot w aRm1) w = N - 2 ^ (64 * w) % N ∧
      word t.mem B (8 * kChecks) = BitVec.ofNat 64 (Proof.RsaKeyGen.checksW w) ∧
      SharedFrame B sp (msRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hnw := hg.scr.nowrap
  have h128 : 128 ≤ Z := by have := hdr_lt_slot w 8 (show 31 < 32 by decide); omega_arith
  have hrun := montSetup_ok M hg hZ hXZ hw hw64 hn hodd htop
  rw [← hm.montSetup] at hrun
  refine WP.mono (WP.of_inline (montSetup_inlineOk hm.ok) henv.hole_clear hrun) ?_
  rintro _ ⟨b, hv, u, rfl, -, mi', hg', hinv, hr2, hr1, hrm, hch, hf, hk⟩
  rw [henv.rsp]
  have hs := fun {d} (h : d + 8 ≤ Z) => henv.patch_word (b := b) (hv := hv) (u := u) h hnw
  have hv' := fun {d} (h : d + 8 * w ≤ Z) => henv.patch_wv (b := b) (hv := hv) (u := u) (k := w) h hnw
  have hsl := fun j (hj : j < 8) => slot_le (w := w) hj
  refine ⟨mi', henv.patch_good hg' h128, ?_, ?_, ?_, ?_, ?_, Frm.patch_shared hf, hk⟩
  · rw [hs (by have := hsl aN (by decide); omega_arith)]; exact hinv
  · rw [hv' (by have := hsl aR2 (by decide); omega_arith)]; exact hr2
  · rw [hv' (by unfold slot aR1 aRm1 at *; omega_arith)]; exact hr1
  · rw [hv' (by omega_arith)]; exact hrm
  · rw [hs (by have := hdr_lt_slot w 8 (show kChecks < 32 by decide); omega_arith)]; exact hch

/-- `sharedWitness_ok`, with calls. -/
theorem sharedWitness_call_ok (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hm : MmCalls M mm)
    {s : State} {B sp : Addr} {Z w : Nat} {mi : BitVec 64} {c bm : Nat} (henv : SharedEnv B Z sp s)
    (hd : MrDims B Z w) (hc : MrCtx s B Z w mi c bm)
    (hR2 : wv s.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c) (hodd : c % 2 = 1) (hc1 : 1 < c)
    (hb : Spec.RsaKeyGen.bitLength (c - 1) = 64 * w)
    {rp : Addr} {used : Nat} {r : List Byte} (hR : word s.mem B (8 * kRand) = rp)
    (hU : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hsrc : Src s B Z rp r) (hlen : used + 8 * w ≤ r.length) :
    WP isa (seqs (mrWitness ++ [mm aXm aX aR2])) s fun t =>
      MrCtx t B Z w mi c bm ∧
      wv t.mem B (slot w aXm) w = (wtOf c w used r).1 % c * 2 ^ (64 * w) % c ∧
      wv t.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c ∧
      word t.mem B (8 * kU) =
        mask (Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w)))).2 ∧
      word t.mem B (8 * kUsed) = BitVec.ofNat 64 (used + 8 * w) ∧
      SharedFrame B sp (witnessRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hnw := hc.good.scr.nowrap
  have hZ := hd.z
  have hx := hd.x
  have hrun := sharedWitness_ok M hd hc hR2 hodd hc1 hb hR hU hK hsrc hlen
  rw [← hm.witness] at hrun
  refine WP.mono (WP.of_inline (witness_inlineOk hm.ok) henv.hole_clear hrun) ?_
  rintro _ ⟨b, hv, u, rfl, -, hcb, hxb, hr2, hu, hus, hf, hk⟩
  rw [henv.rsp]
  have hs := fun {d} (h : d + 8 ≤ Z) => henv.patch_word (b := b) (hv := hv) (u := u) h hnw
  have hv' := fun {d} (h : d + 8 * w ≤ Z) => henv.patch_wv (b := b) (hv := hv) (u := u) (k := w) h hnw
  have hsl := fun j (hj : j < 8) => slot_le (w := w) hj
  refine ⟨henv.patch_mrCtx hcb hd, ?_, ?_, ?_, ?_, Frm.patch_shared hf, hk⟩
  · rw [hv' (by have := hsl aXm (by decide); omega_arith)]; exact hxb
  · rw [hv' (by have := hsl aR2 (by decide); omega_arith)]; exact hr2
  · rw [hs (by have := hdr_lt_slot w 8 (show kU < 32 by decide); omega_arith)]; exact hu
  · rw [hs (by have := hdr_lt_slot w 8 (show kUsed < 32 by decide); omega_arith)]; exact hus

end VG.Proof.RsaKeyGen.X86_64

end

end

/-! # RSA's prepared witness and a generic shared round -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.MillerRabin VG.Proof.MillerRabin.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

def sharedMidRanges (w : Nat) : List (Nat × Nat) := witnessRanges w ++ Caller.callRanges w

theorem sharedKernel_hdr (w j : Nat) (hj : j ∈ [0, 16, 17, 18, 19, 20, 21, 23, 24, 25, 29, 30]) :
    ∀ r ∈ Caller.callRanges w, 8 * j + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * j := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [Caller.callRanges, mutRanges, Proof.MillerRabin.Round.extended, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Caller.pad, slot, hdrBytes, aR1,
      Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
    and_intros <;> omega_arith

private theorem kernel_r2 (w : Nat) :
    ∀ r ∈ Caller.callRanges w, slot w aR2 + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aR2 := by
  simp only [Caller.callRanges, mutRanges, Proof.MillerRabin.Round.extended, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Caller.pad, slot, hdrBytes, aR1, aR2,
    Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
  and_intros <;> omega_arith

private theorem witness_exp (w : Nat) : ∀ r ∈ witnessRanges w, r.1 + r.2 ≤ slot w aE := by
  intro r hr
  simp only [witnessRanges, witRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl) | (rfl | rfl | rfl)
  all_goals simp only [slot, hdrBytes, aX, aAcc, aTmp, aXm, aE, kUsed, kU, sFn]; omega_arith

theorem sharedMid_ok (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hmc : MmCalls M mm) (R : Kernel) {s : State} {B : Addr} {Z w c bm : Nat} {mi : BitVec 64} {sp : Addr}
    (hd : MrDims B Z w) (hZ : slot w 28 ≤ Z) (henv : SharedEnv B Z sp s)
    (hc : MrCtx s B Z w mi c bm) (he : ECtx s.mem B w c)
    (hR2 : wv s.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c) (hc1 : 1 < c)
    (hsh : VG.Proof.RsaKeyGen.PrimeShape (64 * w) c)
    {rp : Addr} {used : Nat} {r : List Byte}
    (hR : word s.mem B (8 * kRand) = rp) (hU : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used)
    (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w)) (hsrc : Src s B Z rp r)
    (hlen : used + 8 * w ≤ r.length)
    {i uni ch : Nat} (hI : word s.mem B (8 * kI) = BitVec.ofNat 64 i)
    (hN : word s.mem B (8 * kUni) = BitVec.ofNat 64 uni) (hC : word s.mem B (8 * kChecks) = BitVec.ofNat 64 ch) :
    WP isa (seqs ((mrWitness ++ [mm aXm aX aR2]) ++ [R.run])) s fun t =>
      (∃ bm', MrCtx t B Z w mi c bm') ∧ ECtx t.mem B w c ∧
      word t.mem B (8 * kFlag) = mask (passOf c w used r) ∧
      word t.mem B (8 * kI) = BitVec.ofNat 64 i ∧ word t.mem B (8 * kUni) = BitVec.ofNat 64 uni ∧
      word t.mem B (8 * kChecks) = BitVec.ofNat 64 ch ∧
      word t.mem B (8 * kU) = mask (wtOf c w used r).2 ∧
      word t.mem B (8 * kUsed) = BitVec.ofNat 64 (used + 8 * w) ∧
      wv t.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c ∧
      SharedFrame B sp (sharedMidRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have ho : c % 2 = 1 := hsh.1
  have hc3 : 3 ≤ c := by omega_arith
  obtain ⟨_, hb, _⟩ := VG.Proof.RsaKeyGen.cand_bits (by have := hd.w4; omega_arith) hsh
  have hn := hc.good.scr.nowrap
  have hz := hd.z
  refine wp_seqs_append (by simp [mrWitness]) (by simp) ?_
  refine WP.mono (sharedWitness_call_ok M hmc henv hd hc hR2 ho hc1 hb hR hU hK hsrc hlen) ?_
  rintro u ⟨hcu, hx, hr2, hu, hus, hfrm, hk⟩
  have heu : ECtx u.mem B w c :=
    ⟨by rw [SharedFrame.array hfrm henv (fun r hr => Or.inr (witness_exp w r hr)) (by have := aE_fits hd; omega_arith) hn]; exact he.e,
      by rw [SharedFrame.word hfrm henv (fun r hr => Or.inr (by have := witness_exp w r hr; omega_arith))
        (by have := aE_fits hd; omega_arith) hn]; exact he.l⟩
  have hx' : wv u.mem B (slot w aXm) w = (wtOf c w used r).1 % c * 2 ^ (64 * w) % c := by
    simpa only [wtOf, Nat.mod_mul_mod] using hx
  have henu := henv.kept hk (by decide)
  simp only [seqs]
  refine WP.mono (R.ok hcu heu hd hZ henu.room ho hc3 hx') ?_
  rintro t ⟨hct, het, hf, hfr, kt⟩
  have hfr : SharedFrame B sp (Caller.callRanges w) u.mem t.mem := by
    rw [henu.rsp] at hfr
    exact hfr
  have hfm : SharedFrame B sp (sharedMidRanges w) s.mem t.mem :=
    (hfrm.mono (fun r hr => List.mem_append_left _ hr)).trans
      (hfr.mono (fun r hr => List.mem_append_right _ hr))
  refine ⟨hct, het, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfm, (hk.trans kt).mono (by decide)⟩
  · simpa only [Proof.MillerRabin.Round.round, passOf] using hf
  · rw [SharedFrame.word hfm henv (d := 8 * kI) ?_ (by have := hdr_lt_slot w 28 (show kI < 32 by decide); omega_arith) hn]
    · exact hI
    · intro r hr
      rcases List.mem_append.mp hr with hw | hk
      · simp only [witnessRanges, witRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with (rfl | rfl | rfl) | (rfl | rfl | rfl) <;> rng_disj
      · exact sharedKernel_hdr w kI (by simp [kI, kElen, sFn]) r hk
  · rw [SharedFrame.word hfm henv (d := 8 * kUni) ?_ (by have := hdr_lt_slot w 28 (show kUni < 32 by decide); omega_arith) hn]
    · exact hN
    · intro r hr
      rcases List.mem_append.mp hr with hw | hk
      · simp only [witnessRanges, witRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with (rfl | rfl | rfl) | (rfl | rfl | rfl) <;> rng_disj
      · exact sharedKernel_hdr w kUni (by simp [kUni, kP, sFn]) r hk
  · rw [SharedFrame.word hfm henv (d := 8 * kChecks) ?_ (by have := hdr_lt_slot w 28 (show kChecks < 32 by decide); omega_arith) hn]
    · exact hC
    · intro r hr
      rcases List.mem_append.mp hr with hw | hk
      · simp only [witnessRanges, witRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with (rfl | rfl | rfl) | (rfl | rfl | rfl) <;> rng_disj
      · exact sharedKernel_hdr w kChecks (by simp [kChecks, kE, sFn]) r hk
  · rw [SharedFrame.word hfr henv (sharedKernel_hdr w kU (by simp [kU, sFn])) (by have := hdr_lt_slot w 28 (show kU < 32 by decide); omega_arith) hn]
    exact hu
  · rw [SharedFrame.word hfr henv (sharedKernel_hdr w kUsed (by simp [kUsed, sFn])) (by have := hdr_lt_slot w 28 (show kUsed < 32 by decide); omega_arith) hn]
    exact hus
  · have hslot := slot_le (w := w) (show aR2 < 8 by decide)
    rw [SharedFrame.array hfr henv (kernel_r2 w) (by omega_arith) hn]
    exact hr2

end VG.Proof.RsaKeyGen.X86_64

end

end

/-! ### `RsaKeyGen.X86_64.SharedRanges`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86_64.SharedRound`, which this module and modules that import it used -/

section

/-! # RSA's witness policy around the callable shared round -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.MillerRabin.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

def sharedRoundRanges (w : Nat) : List (Nat × Nat) :=
  sharedMidRanges w ++ [(8 * kI, 8), (8 * kUni, 8), (8 * kStat, 8)]

/-- `mrRoundWith`. -/
theorem sharedRound_ok (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hmc : MmCalls M mm) (R : Kernel) {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm : Nat} {sp : Addr}
    (hd : MrDims B Z w) (hZ : slot w 28 ≤ Z) (henv : SharedEnv B Z sp s) (hc : MrCtx s B Z w mi c bm) (hE : ECtx s.mem B w c)
    (hR2 : wv s.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c) (hc1 : 1 < c)
    (hsh : VG.Proof.RsaKeyGen.PrimeShape (64 * w) c)
    {rp : Addr} {used : Nat} {r : List Byte} (hR : word s.mem B (8 * kRand) = rp)
    (hU : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hsrc : Src s B Z rp r) (hlen : used + 8 * w ≤ r.length)
    {i uni ch : Nat} (hI : word s.mem B (8 * kI) = BitVec.ofNat 64 i)
    (hN : word s.mem B (8 * kUni) = BitVec.ofNat 64 uni) (hC : word s.mem B (8 * kChecks) = BitVec.ofNat 64 ch)
    (hi : i < 2 ^ 61) (huni : uni < 2 ^ 61) (hch : ch < 2 ^ 62) :
    WP isa (seqs (mrRoundWith mm R.run)) s fun t =>
      (∃ bm', MrCtx t B Z w mi c bm') ∧ ECtx t.mem B w c ∧
      wv t.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c ∧
      word t.mem B (8 * kUsed) = BitVec.ofNat 64 (used + 8 * w) ∧
      word t.mem B (8 * kStat) = BitVec.ofNat 64
        (if Spec.RsaKeyGen.mrIteration c (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2
            (Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w)))).1 then
          (if i + 1 < 17 ∨ uni + (Spec.RsaKeyGen.witness (c - 1)
              (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w)))).2.toNat < ch then 4 else 1)
        else 3) ∧
      (Spec.RsaKeyGen.mrIteration c (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2
          (Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w)))).1 = true →
        word t.mem B (8 * kI) = BitVec.ofNat 64 (i + 1) ∧
        word t.mem B (8 * kUni) = BitVec.ofNat 64 (uni + (Spec.RsaKeyGen.witness (c - 1)
          (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w)))).2.toNat)) ∧
      SharedFrame B sp (sharedRoundRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.good.scr.nowrap
  rw [mrRoundWith]
  refine wp_seqs_append (by simp [mrWitness]) (by simp) ?_
  refine WP.mono (sharedMid_ok M hmc R hd hZ henv hc hE hR2 hc1 hsh hR hU hK hsrc hlen hI hN hC)
    fun s₂ ⟨⟨bm₂, hc₂⟩, he₂, hfl₂, hI₂, hN₂, hC₂, hU₂, hUs₂, hR2₂, hf02, k₁₂⟩ => ?_
  simp only [wtOf, passOf] at hU₂ hfl₂
  generalize hwt : Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w))) = wt
    at hU₂ hfl₂ ⊢
  generalize hfv : Spec.RsaKeyGen.mrIteration c (Spec.Rsa.splitTwos (c - 1)).1
    (Spec.Rsa.splitTwos (c - 1)).2 wt.1 = f at hfl₂ ⊢
  have hg₂ := hc₂.good
  refine WP.mono (roundTail_ok hg₂ hd.z hfl₂ hI₂ hU₂ hN₂ hC₂ (by omega_arith) (by omega_arith) hch) fun t ⟨hm, k⟩ => ?_
  have hft : Frm B [(8 * kI, 8), (8 * kUni, 8), (8 * kStat, 8)] s₂.mem t.mem := by
    rw [hm]
    have wI := Frm.of_outside (rs := [(8 * kI, 8), (8 * kUni, 8), (8 * kStat, 8)])
      (writeW_outside s₂.mem B (BitVec.ofNat 64 (i + 1)) (d := 8 * kI) (by unfold kI kElen sFn; omega_arith)) (by simp)
    cases f
    · exact Frm.of_outside (writeW_outside _ B _ (d := 8 * kStat) (by unfold kStat sFn; omega_arith)) (by simp)
    · exact (wI.trans (Frm.of_outside (writeW_outside _ B _ (d := 8 * kUni) (by unfold kUni kP sFn; omega_arith))
        (by simp))).trans (Frm.of_outside (writeW_outside _ B _ (d := 8 * kStat) (by unfold kStat sFn; omega_arith))
        (by simp))
  have hgt : Good t B Z w mi := ⟨hg₂.scr.congr k.2.2, (k.gpr (by decide)).trans hg₂.rdi,
    Hdr.of_frm hg₂.hdr hft (by rng_disj)⟩
  refine ⟨⟨bm₂, hc₂.of_frm hd hft hgt.scr hgt.rdi (by rng_disj) (by rng_disj) (by rng_disj) (by rng_disj) (by rng_disj)⟩,
    he₂.of_frm hft (by rng_disj) (by have := aE_fits hd; omega_arith),
    ?_, ?_, ?_, ?_, ?_, ((k₁₂.trans k).mono (by decide))⟩
  · rw [hft.wv_eq (d := slot w aR2) (k := w) (by rng_disj)
      (by have := slot_le (w := w) (show aR2 < 8 by decide); have := hd.z; omega_arith)]; exact hR2₂
  · rw [hft.word_eq (d := 8 * kUsed) (by rng_disj) (by unfold kUsed sFn; omega_arith)]; exact hUs₂
  · rw [hm]; cases f <;> simp only [↓reduceIte, Bool.false_eq_true, word_writeW_self]
  · intro hf
    rw [hm, hf]
    simp only [↓reduceIte]
    refine ⟨?_, ?_⟩
    · rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        word_writeW_self]
    · rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · exact (hf02.mono (fun r hr => List.mem_append_left _ hr)).trans
      (hft.work.mono (fun r hr => List.mem_append_right _ hr))

end VG.Proof.RsaKeyGen.X86_64

end

end

/-! # Workspace bounds and protected headers of an RSA witness round -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.MillerRabin
open VG.Proof.MillerRabin.X86_64

theorem sharedRoundRanges_le (w : Nat) : ∀ r ∈ sharedRoundRanges w, r.1 + r.2 ≤ slot w 28 := by
  simp only [sharedRoundRanges, sharedMidRanges, witnessRanges, witRanges, Caller.callRanges,
    mutRanges, Proof.MillerRabin.Round.extended, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Caller.pad, slot, hdrBytes, aR1, aX, aAcc, aTmp, aXm, kUsed, kU, kI, kUni, kStat,
    kElen, kP, sFn, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
  and_intros <;> omega_arith

theorem sharedRoundRanges_hdr (w : Nat) {k : Nat}
    (hk : k = kRand ∨ k = kLen ∨ k = kRandLen ∨ k = kChecks ∨ k = kOut ∨ k = kUsedP) :
    ∀ r ∈ sharedRoundRanges w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [sharedRoundRanges, sharedMidRanges, witnessRanges, witRanges, Caller.callRanges,
    mutRanges, Proof.MillerRabin.Round.extended, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Caller.pad, slot, hdrBytes, aR1, aX, aAcc, aTmp, aXm, kUsed, kU, kI, kUni, kStat,
    kElen, kP, sFn, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes, kRand, kLen, kRandLen, kChecks, kE, kOut, kUsedP]
    and_intros <;> omega_arith

theorem sharedRoundRanges_low (w : Nat) : ∀ r ∈ sharedRoundRanges w, 48 ≤ r.1 := by
  simp only [sharedRoundRanges, sharedMidRanges, witnessRanges, witRanges, Caller.callRanges,
    mutRanges, Proof.MillerRabin.Round.extended, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Caller.pad, slot, hdrBytes, aR1, aX, aAcc, aTmp, aXm, kUsed, kU, kI, kUni, kStat,
    kElen, kP, sFn, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
  and_intros <;> omega_arith

end VG.Proof.RsaKeyGen.X86_64

end

end

/-! # RSA's witness loop with an actual callable prepared round -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.MillerRabin.X86_64
open VG.Proof.MlKem.X86_64

/-- At the head of the loop, after `i − 1` witnesses (`uni` of them uniform)
and `used` octets of `rand`. -/
structure SharedMrSt (B sp : Addr) (Z w : Nat) (mi : BitVec 64) (c ch : Nat) (rp : Addr) (r : List Byte) (s₀ : State)
    (res : Option (Bool × List Byte)) (i uni used : Nat) (s : State) : Prop where
  ctx : ∃ bm, MrCtx s B Z w mi c bm
  ex : ECtx s.mem B w c
  r2 : wv s.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c
  rand : word s.mem B (8 * kRand) = rp
  len : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w)
  rlen : word s.mem B (8 * kRandLen) = BitVec.ofNat 64 r.length
  chk : word s.mem B (8 * kChecks) = BitVec.ofNat 64 ch
  src : Src s B Z rp r
  ki : word s.mem B (8 * kI) = BitVec.ofNat 64 i
  kuni : word s.mem B (8 * kUni) = BitVec.ofNat 64 uni
  kused : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used
  ul : used ≤ r.length
  go : i ≤ Spec.RsaKeyGen.blindedChecks ∨ uni < ch
  iu : 8 * w * i ≤ used
  unii : uni ≤ i
  rest : mrRest c ch r i uni used = res
  frm : SharedFrame B sp (sharedRoundRanges w) s₀.mem s.mem
  keep : Keep mmRegs s₀ s
  env : SharedEnv B Z sp s

/-- How the loop ends. -/
abbrev SharedMrEnd (B sp : Addr) (Z w : Nat) (mi : BitVec 64) (c : Nat) (r : List Byte) (s₀ : State)
    (res : Option (Bool × List Byte)) (s : State) : Prop :=
  (∃ bm, MrCtx s B Z w mi c bm) ∧
  (res = none → word s.mem B (8 * kStat) = BitVec.ofNat 64 0) ∧
  (∀ b rest, res = some (b, rest) → word s.mem B (8 * kStat) = BitVec.ofNat 64 (if b then 1 else 3) ∧
    word s.mem B (8 * kUsed) = BitVec.ofNat 64 (r.length - rest.length)) ∧
  SharedFrame B sp (sharedRoundRanges w) s₀.mem s.mem ∧ Keep mmRegs s₀ s

/-- One iteration of `millerRabinWith`'s loop. -/
theorem sharedMrIter_ok (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hmc : MmCalls M mm) (R : Kernel) {B sp : Addr} {Z w : Nat} {mi : BitVec 64} {c ch : Nat} {rp : Addr} {r : List Byte}
    {s₀ : State} {res : Option (Bool × List Byte)} (hd : MrDims B Z w) (hZ28 : slot w 28 ≤ Z) (hc1 : 1 < c)
    (hsh : VG.Proof.RsaKeyGen.PrimeShape (64 * w) c) (hrl : r.length < 2 ^ 64) (hch : ch < 2 ^ 62)
    {i uni used : Nat} (s : State) (hI : SharedMrSt B sp Z w mi c ch rp r s₀ res i uni used s) :
    WP isa (seqs [
      .block [.mov .rcx (.mem (hdr kRandLen)), .mov .rax (.mem (hdr kUsed)), .alu .sub .rcx (.reg .rax),
        .mov .rax (.mem (hdr kLen)), .alu .cmp .rcx (.reg .rax)],
      .ite .b (.block [.mov32 .rax (.imm 0), .store (hdr kStat) .rax]) (seqs (mrRoundWith mm R.run)),
      .block [.mov .rax (.mem (hdr kStat)), .alu .cmp .rax (.imm 4)]]) s fun s' =>
      (isa.eval .e s' = some false ∧ SharedMrEnd B sp Z w mi c r s₀ res s' ∧ (res = none → r.length < used + 8 * w) ∧
        (∀ b rest, res = some (b, rest) → rest.length + (used + 8 * w) = r.length)) ∨
      (isa.eval .e s' = some true ∧ ∃ uni', SharedMrSt B sp Z w mi c ch rp r s₀ res (i + 1) uni' (used + 8 * w) s') := by
  obtain ⟨⟨bm, hc⟩, hE, hr2, hrp, hlen, hrlen, hchk, hsrc, hi, hun, hus, hul, hgo, hiu, huni, hres, hfrm, hkeep, henv⟩ := hI
  have hg := hc.good
  obtain hEn : B.toNat + slot w aE + 8 * (w + 1) ≤ 2 ^ 64 := by
    have := aE_fits hd; have := hd.z; have := hg.scr.nowrap; omega_arith
  have hZ := hd.z
  have hw4 := hd.w4
  have hnw := hg.scr.nowrap
  obtain ⟨_, _, hwb⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega_arith) hsh
  obtain hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  obtain hres' := VG.Proof.RsaKeyGen.mrLoop_step c ch (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2
    (8 * w) r i uni used hgo hwb (by omega_arith)
  simp only [seqs]
  obtain e1 : BitVec.ofNat 64 r.length - BitVec.ofNat 64 used = BitVec.ofNat 64 (r.length - used) :=
    ofNat_sub_ofNat' hul hrl
  obtain e2 : r.length - used < 2 ^ 64 := by omega_arith
  obtain e3 : 8 * w < 2 ^ 64 := by have := hd.w128; omega_arith
  refine WP.seq (WP.mono (WP.keep [.rcx, .rax] (Q := fun t => t.cf = some (decide (r.length < used + 8 * w)) ∧
      t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl kUsed (by decide), hl kLen (by decide), hl kRandLen (by decide), hus, hlen,
      hrlen, e1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt e2, Nat.mod_eq_of_lt e3]
    exact decide_eq_decide.mpr (by omega_arith)) rfl) fun s₁ ⟨⟨hcf, hm₁⟩, k₁⟩ => ?_)
  obtain hg₁ : Good s₁ B Z w mi := ⟨hg.scr.congr k₁.2.2, (k₁.gpr (by decide)).trans hg.rdi, by rw [hm₁]; exact hg.hdr⟩
  refine WP.seq (WP.ite (decide (r.length < used + 8 * w)) (by simp [eval, hcf]) (fun h => ?_) (fun h => ?_))
  · -- Out of octets: `kStat := 0`.
    simp only [decide_eq_true_eq] at h
    obtain hst : InRegions s₁.wr (off B (8 * kStat)) 8 :=
      hg₁.scr.st (by have := hdr_lt_slot w 8 (show kStat < 32 by decide); omega_arith)
    refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s₁.mem.writeW (off B (8 * kStat)) (BitVec.ofNat 64 0)) (by
      xrun [State.ea, hdr, hg₁.rdi, hdrOff, hst]; rfl) rfl) fun s₂ ⟨hm₂, k₂⟩ => ?_
    obtain hf₂ : Frm B [(8 * kStat, 8)] s.mem s₂.mem := by
      rw [hm₂, hm₁]; exact Frm.of_outside (writeW_outside _ B _ (d := 8 * kStat) (by unfold kStat sFn; omega_arith)) (by simp)
    obtain hg₂ : Good s₂ B Z w mi := ⟨hg₁.scr.congr k₂.2.2, (k₂.gpr (by decide)).trans hg₁.rdi,
      Hdr.of_frm hg.hdr hf₂ (by rng_disj)⟩
    refine WP.mono (statCmp_ok hg₂ hZ (v := 0) (by decide) (by rw [hm₂, word_writeW_self]))
      fun t ⟨hz, hm, k⟩ => Or.inl ⟨by simp [eval, hz], ?_⟩
    obtain hres0 : res = none := hres.symm.trans (hres'.trans (ite_f (by omega_arith) _ _))
    obtain hft : Frm B [(8 * kStat, 8)] s.mem t.mem :=
      hf₂.trans (show Frm B [(8 * kStat, 8)] s₂.mem t.mem by rw [hm]; exact Frm.refl _ _ _)
    refine ⟨⟨⟨bm, hc.of_frm hd hft (hg₂.scr.congr k.2.2)
        ((k.gpr (by decide)).trans hg₂.rdi) (by rng_disj) (by rng_disj) (by rng_disj) (by rng_disj) (by rng_disj)⟩,
      ?_, ?_, ?_, (((hkeep.trans k₁).trans k₂).trans k).mono (by decide)⟩, fun _ => h,
      fun b rest h1 => by rw [hres0] at h1; cases h1⟩
    · intro _; rw [hm, hm₂, word_writeW_self]
    · intro b rest h; rw [hres0] at h; cases h
    · exact hfrm.trans (hft.work.mono (by simp [sharedRoundRanges]))
  · -- A round.
    simp only [decide_eq_false_iff_not, Nat.not_lt] at h
    obtain hc₁ : MrCtx s₁ B Z w mi c bm := hc.of_frm hd (rs := []) (by rw [hm₁]; exact Frm.refl _ _ _) hg₁.scr
      hg₁.rdi (by simp) (by simp) (by simp) (by simp) (by simp)
    obtain hi61 : i < 2 ^ 61 := by
      have : 32 * i ≤ 8 * w * i := Nat.mul_le_mul_right _ (by omega_arith)
      omega_arith
    refine WP.mono (sharedRound_ok (rp := rp) (used := used) (r := r) (i := i) (uni := uni) (ch := ch) M hmc R hd hZ28 (henv.kept k₁ (by decide)) hc₁
      (by rw [hm₁]; exact hE) (by rw [hm₁]; exact hr2) hc1 hsh (by rw [hm₁]; exact hrp)
      (by rw [hm₁]; exact hus) (by rw [hm₁]; exact hlen) (hsrc.congrK (by rw [hm₁]; exact InScr.refl _ _ _) k₁) h
      (by rw [hm₁]; exact hi) (by rw [hm₁]; exact hun) (by rw [hm₁]; exact hchk) hi61 (by omega_arith) hch)
      fun s₂ ⟨⟨bm₂, hc₂⟩, he₂, hr₂, hus₂, hst₂, hcnt₂, hfr₂, k₂⟩ => ?_
    rw [ite_t h] at hres'
    generalize hwt : Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w))) = wt
      at hres' hst₂ hcnt₂
    generalize hfv : Spec.RsaKeyGen.mrIteration c (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2 wt.1 = f
      at hres' hst₂ hcnt₂
    obtain hfr : SharedFrame B sp (sharedRoundRanges w) s.mem s₂.mem := by rw [← hm₁]; exact hfr₂
    obtain hdrop : r.length - (r.drop (used + 8 * w)).length = used + 8 * w := by rw [List.length_drop]; omega_arith
    obtain hk : Keep mmRegs s₀ s₂ := ((hkeep.trans k₁).trans k₂).mono (by decide)
    refine WP.mono (statCmp_ok hc₂.good hZ (v := if f then (if i + 1 < 17 ∨ uni + wt.2.toNat < ch then 4 else 1) else 3)
      (by split <;> (try split) <;> decide) hst₂) fun t ⟨hz, hm, k⟩ => ?_
    obtain hct : MrCtx t B Z w mi c bm₂ := hc₂.of_frm hd (rs := [])
      (by rw [hm]; exact Frm.refl _ _ _) (hc₂.good.scr.congr k.2.2) ((k.gpr (by decide)).trans hc₂.good.rdi)
      (by simp) (by simp) (by simp) (by simp) (by simp)
    obtain hkt : Keep mmRegs s₀ t := (hk.trans k).mono (by decide)
    obtain hft : SharedFrame B sp (sharedRoundRanges w) s₀.mem t.mem := by rw [hm]; exact hfrm.trans hfr
    cases f
    · -- Composite.
      refine Or.inl ⟨by simp [eval, hz], ⟨⟨_, hct⟩, fun h0 => ?_, fun b rest h1 => ?_, hft, hkt⟩, fun h0 => ?_,
        fun b rest h1 => ?_⟩
      · have h0' := hres'.symm.trans (hres.trans h0); simp at h0'
      · have h1' := hres'.symm.trans (hres.trans h1)
        simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h1'
        obtain ⟨h1a, h1b⟩ := h1'
        subst h1a h1b
        rw [hm, hst₂, hus₂, hdrop]; exact ⟨rfl, rfl⟩
      · have h0' := hres'.symm.trans (hres.trans h0); simp at h0'
      · have h1' := hres'.symm.trans (hres.trans h1)
        simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h1'
        obtain ⟨-, h1b⟩ := h1'
        subst h1b
        rw [List.length_drop]; omega_arith
    · obtain ⟨hI₂, hN₂⟩ := hcnt₂ rfl
      obtain hu : (if wt.2 = true then 1 else 0) = wt.2.toNat := by cases wt.2 <;> rfl
      simp only [↓reduceIte, hu] at hres'
      by_cases hcnd : i + 1 < 17 ∨ uni + wt.2.toNat < ch
      · -- On to the next witness.
        refine Or.inr ⟨by simp [eval, hz, hcnd], uni + wt.2.toNat, ⟨⟨_, hct⟩,
          (by rw [hm]; exact he₂), ?_, ?_, ?_, ?_, ?_,
          ?_, by rw [hm]; exact hI₂, by rw [hm]; exact hN₂, by rw [hm]; exact hus₂, by omega_arith, ?_, ?_, ?_, ?_, hft,
          hkt, henv.kept ((k₁.trans k₂).trans k) (by decide)⟩⟩
        · rw [hm]; exact hr₂
        · rw [hm, SharedFrame.word hfr henv (sharedRoundRanges_hdr w (Or.inl rfl)) (by have := hdr_lt_slot w 28 (show kRand < 32 by decide); omega_arith) hnw]; exact hrp
        · rw [hm, SharedFrame.word hfr henv (sharedRoundRanges_hdr w (Or.inr (Or.inl rfl))) (by have := hdr_lt_slot w 28 (show kLen < 32 by decide); omega_arith) hnw]; exact hlen
        · rw [hm, SharedFrame.word hfr henv (sharedRoundRanges_hdr w (Or.inr (Or.inr (Or.inl rfl)))) (by have := hdr_lt_slot w 28 (show kRandLen < 32 by decide); omega_arith) hnw]
          exact hrlen
        · rw [hm, SharedFrame.word hfr henv (sharedRoundRanges_hdr w (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (by have := hdr_lt_slot w 28 (show kChecks < 32 by decide); omega_arith) hnw]
          exact hchk
        · have hle : ∀ r ∈ sharedRoundRanges w, r.1 + r.2 ≤ Z := fun r hr => by
            have := sharedRoundRanges_le w r hr; have := hZ28; omega_arith
          exact hsrc.shared henv (by rw [hm]; exact hfr) hle ((k₁.trans k₂).trans k)
        · exact hcnd.imp (fun h => show i + 1 ≤ 16 by omega_arith) id
        · rw [Nat.mul_add, Nat.mul_one]; omega_arith
        · cases wt.2 <;> simp <;> omega_arith
        · exact hres'.symm.trans hres
      · -- Probably prime.
        obtain hdone := VG.Proof.RsaKeyGen.mrLoop_done c ch (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2
          (r.drop (used + 8 * w)) (i + 1) (uni + wt.2.toNat)
          (by intro h; exact hcnd (h.imp (fun h => by unfold Spec.RsaKeyGen.blindedChecks at h; omega_arith) id))
        refine Or.inl ⟨by simp [eval, hz, hcnd], ⟨⟨_, hct⟩, fun h0 => ?_, fun b rest h1 => ?_, hft, hkt⟩,
          fun h0 => ?_, fun b rest h1 => ?_⟩
        · have h0' := (hres'.symm.trans (hres.trans h0)); rw [hdone] at h0'; cases h0'
        · have h1' := (hres'.symm.trans (hres.trans h1))
          rw [hdone] at h1'
          simp only [Option.some.injEq, Prod.mk.injEq] at h1'
          obtain ⟨h1a, h1b⟩ := h1'
          subst h1a h1b
          rw [hm, hst₂, hus₂, hdrop]
          simp [hcnd]
        · have h0' := (hres'.symm.trans (hres.trans h0)); rw [hdone] at h0'; cases h0'
        · have h1' := (hres'.symm.trans (hres.trans h1))
          rw [hdone] at h1'
          simp only [Option.some.injEq, Prod.mk.injEq] at h1'
          obtain ⟨-, h1b⟩ := h1'
          subst h1b
          rw [List.length_drop]; omega_arith

/-- The start of `millerRabinWith`: `kI := 1`, `kUni := 0`. -/
theorem sharedMrInit_ok {B sp : Addr} {Z w : Nat} {mi : BitVec 64} {c ch bm : Nat} {rp : Addr}
    {r : List Byte} {s : State} {used : Nat} (hd : MrDims B Z w) (_hZ28 : slot w 28 ≤ Z)
    (henv : SharedEnv B Z sp s) (hc : MrCtx s B Z w mi c bm) (hE : ECtx s.mem B w c)
    (hr2 : wv s.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c)
    (hrp : word s.mem B (8 * kRand) = rp) (hlen : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hrlen : word s.mem B (8 * kRandLen) = BitVec.ofNat 64 r.length)
    (hchk : word s.mem B (8 * kChecks) = BitVec.ofNat 64 ch) (hsrc : Src s B Z rp r)
    (hus : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used) (hu1 : 8 * w ≤ used) (hu2 : used ≤ r.length) :
    WP isa (.block [.mov32 .rax (.imm 1), .store (hdr kI) .rax, .mov32 .rax (.imm 0), .store (hdr kUni) .rax]) s
      (SharedMrSt B sp Z w mi c ch rp r s (mrRest c ch r 1 0 used) 1 0 used) := by
  have hg := hc.good
  have hZ := hd.z
  have hnw := hg.scr.nowrap
  obtain hs : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8 := fun i hi =>
    hg.scr.st (by have := hdr_lt_slot w 8 hi; omega_arith)
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = (s.mem.writeW (off B (8 * kI)) (BitVec.ofNat 64 1)).writeW
      (off B (8 * kUni)) (BitVec.ofNat 64 0)) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hs kI (by decide), hs kUni (by decide)]
    rfl) rfl) fun s₁ ⟨hm₁, k₁⟩ => ?_
  obtain hf₁ : Frm B [(8 * kI, 8), (8 * kUni, 8)] s.mem s₁.mem := by
    rw [hm₁]
    exact (Frm.of_outside (writeW_outside _ B _ (d := 8 * kI) (by unfold kI kElen sFn; omega_arith)) (by simp)).trans
      (Frm.of_outside (writeW_outside _ B _ (d := 8 * kUni) (by unfold kUni kP sFn; omega_arith)) (by simp))
  obtain hg₁ : Good s₁ B Z w mi := ⟨hg.scr.congr k₁.2.2, (k₁.gpr (by decide)).trans hg.rdi,
    Hdr.of_frm hg.hdr hf₁ (by rng_disj)⟩
  obtain hh : ∀ {k}, k = kRand ∨ k = kLen ∨ k = kRandLen ∨ k = kChecks ∨ k = kUsed ∨ k = kOut →
      word s₁.mem B (8 * k) = word s.mem B (8 * k) := fun {k} hk => by
    rw [hm₁]
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]
  refine ⟨⟨bm, hc.of_frm hd hf₁ hg₁.scr hg₁.rdi (by rng_disj) (by rng_disj) (by rng_disj) (by rng_disj)
      (by rng_disj)⟩, hE.of_frm hf₁ (by rng_disj) (by have := aE_fits hd; have := hd.z; have := hg.scr.nowrap; omega_arith), ?_, by rw [hh (Or.inl rfl)]; exact hrp, by rw [hh (Or.inr (Or.inl rfl))]; exact hlen,
    by rw [hh (Or.inr (Or.inr (Or.inl rfl)))]; exact hrlen, by rw [hh (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]; exact hchk,
    hsrc.congrK (InScr.of_frm hf₁ (by
      have := hdr_lt_slot w 8 (show 31 < 32 by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, kI, kElen, kUni, kP, sFn]
      omega_arith)) k₁,
    by rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self],
    by rw [hm₁, word_writeW_self], by rw [hh (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))]; exact hus, hu2,
    Or.inl (by decide), by omega_arith, by omega_arith, rfl,
    hf₁.work.mono (by simp [sharedRoundRanges]), k₁.mono (by decide), henv.kept k₁ (by decide)⟩
  rw [hf₁.wv_eq (d := slot w aR2) (k := w) (by rng_disj)
    (by have := slot_le (w := w) (show aR2 < 8 by decide); omega_arith)]; exact hr2


/-- `millerRabinWith`: the witnesses from offset `used`, as `primalityTest`'s
loop from `(1, 0)`. -/
theorem sharedMillerRabin_ok (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hmc : MmCalls M mm) (R : Kernel) {B sp : Addr} {Z w : Nat} {mi : BitVec 64} {c ch bm : Nat} {rp : Addr}
    {r : List Byte} {s : State} {used : Nat} (hd : MrDims B Z w) (hZ28 : slot w 28 ≤ Z) (hc1 : 1 < c)
    (hsh : VG.Proof.RsaKeyGen.PrimeShape (64 * w) c) (hrl : r.length < 2 ^ 64) (hch : ch < 2 ^ 62)
    (henv : SharedEnv B Z sp s) (hc : MrCtx s B Z w mi c bm) (hE : ECtx s.mem B w c)
    (hr2 : wv s.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c)
    (hrp : word s.mem B (8 * kRand) = rp) (hlen : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hrlen : word s.mem B (8 * kRandLen) = BitVec.ofNat 64 r.length)
    (hchk : word s.mem B (8 * kChecks) = BitVec.ofNat 64 ch) (hsrc : Src s B Z rp r)
    (hus : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used) (hu1 : 8 * w ≤ used) (hu2 : used ≤ r.length) :
    WP isa (seqs (millerRabinWith mm R.run)) s (SharedMrEnd B sp Z w mi c r s (mrRest c ch r 1 0 used)) := by
  unfold millerRabinWith
  simp only [seqs]
  refine WP.seq (WP.mono (sharedMrInit_ok hd hZ28 henv hc hE hr2 hrp hlen hrlen hchk hsrc hus hu1 hu2) fun s₁ h => ?_)
  exact WP.loop (fun n t => ∃ i uni u, n = r.length - u ∧ SharedMrSt B sp Z w mi c ch rp r s (mrRest c ch r 1 0 used) i uni u t)
    (fun n t ⟨i, uni, u, hn, hI⟩ => WP.mono (sharedMrIter_ok M hmc R hd hZ28 hc1 hsh hrl hch t hI) fun t' h => h.imp (fun h => ⟨h.1, h.2.1⟩)
      fun ⟨he, uni', hI'⟩ => ⟨he, r.length - (u + 8 * w), by have := hI'.ul; have := hd.w4; omega_arith,
        i + 1, uni', u + 8 * w, rfl, hI'⟩) (r.length - used) s₁ ⟨1, 0, used, rfl, h⟩

end VG.Proof.RsaKeyGen.X86_64

end

end

/-! ### `RsaKeyGen.X86_64.SharedEnd`, which only this module used -/

section

/-! # Candidate finalization with the shared callee's private stack -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.MlKem.X86_64

structure SharedKEnd (s t : State) (B sp : Addr) (Z : Nat) (op up : Addr)
    (k st u : Nat) (outv : Option Nat) : Prop where
  rax : t.gpr .rax = BitVec.ofNat 64 st
  used : t.mem.readW up 64 = BitVec.ofNat 64 u
  out : outBytes t.mem op k = match outv with
    | some c => Spec.Rsa.i2osp c k
    | none => outBytes s.mem op k
  saved : ∀ i < 6, t.gpr (saved.getD i .rax) = word s.mem B (8 * i)
  frame : ∀ x, ¬(below sp 128).Contains x 1 → Z ≤ ofs B x →
    (∀ b < 8, x ≠ up + BitVec.ofNat 64 b) → (∀ j < k, x ≠ op + BitVec.ofNat 64 j) →
    t.mem x = s.mem x
  keep : Keep mmRegs s t

theorem KEnd.shared {s t : State} {B sp : Addr} {Z : Nat} {op up : Addr}
    {k st u : Nat} {outv : Option Nat} (h : KEnd s t B Z op up k st u outv) :
    SharedKEnd s t B sp Z op up k st u outv :=
  ⟨h.rax, h.used, h.out, h.saved, fun x _ hx hu ho => h.frame x hx hu ho, h.keep⟩

theorem SharedKEnd.trans_pre {s₀ s t : State} {B sp : Addr} {Z : Nat} {op up : Addr}
    {k st u : Nat} {outv : Option Nat}
    (h : SharedKEnd s t B sp Z op up k st u outv)
    (hlo : ∀ i < 6, word s.mem B (8 * i) = word s₀.mem B (8 * i))
    (hhi : ∀ x, ¬(below sp 128).Contains x 1 → Z ≤ ofs B x → s.mem x = s₀.mem x)
    (hout : ∀ j < k, s.mem (op + BitVec.ofNat 64 j) = s₀.mem (op + BitVec.ofNat 64 j))
    (hk : Keep mmRegs s₀ s) : SharedKEnd s₀ t B sp Z op up k st u outv := by
  refine ⟨h.rax, h.used, ?_, fun i hi => (h.saved i hi).trans (hlo i hi),
    fun x he hx hu ho => (h.frame x he hx hu ho).trans (hhi x he hx),
    (hk.trans h.keep).mono (by decide)⟩
  rw [h.out]
  cases outv
  · exact List.map_congr_left fun i hi => hout i (List.mem_range.mp hi)
  · rfl

def SharedCandEnd (s t : State) (B sp : Addr) (Z : Nat) (op up : Addr) (k : Nat) (r : List Byte) :
    Option (Spec.RsaKeyGen.Candidate × List Byte) → Prop
  | none => SharedKEnd s t B sp Z op up k 0 0 none
  | some (.prime c, rest) => SharedKEnd s t B sp Z op up k 1 (r.length - rest.length) (some c)
  | some (.close, rest) => SharedKEnd s t B sp Z op up k 2 (r.length - rest.length) none
  | some (.rejected, rest) => SharedKEnd s t B sp Z op up k 3 (r.length - rest.length) none

theorem sharedFinUsed_end {s sX : State} {B sp : Addr} {Z : Nat} {op up : Addr} {k st u : Nat}
    (hs : Scr sX B Z) (hdi : sX.gpr .rdi = B) (h8 : 8 * 32 ≤ Z) (hst : st < 2 ^ 31)
    (hu : word sX.mem B (8 * kUsed) = BitVec.ofNat 64 u)
    (hU : word sX.mem B (8 * kUsedP) = up) (ho : OutUp sX B Z op up k)
    (hlo : ∀ i < 6, word sX.mem B (8 * i) = word s.mem B (8 * i))
    (hhi : InScr B Z s.mem sX.mem) (kk : Keep mmRegs s sX) :
    WP isa (finUsed st) sX fun t => SharedKEnd s t B sp Z op up k st u none :=
  WP.mono (finUsed_end hs hdi h8 hst hu hU ho hlo hhi kk) fun _ h => h.shared

end VG.Proof.RsaKeyGen.X86_64

end

end

/-! ### `RsaKeyGen.X86_64.SharedTail`, which only this module used -/

section

/-! # Montgomery setup and RSA's shared Miller–Rabin witness loop -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.MillerRabin.X86_64
open VG.Proof.MlKem.X86_64

/-- How a primality test's result ends a candidate `c`. -/
def SharedTestEnd (s t : State) (B sp : Addr) (Z : Nat) (op up : Addr) (k : Nat) (r : List Byte) (c : Nat) :
    Option (Bool × List Byte) → Prop
  | none => SharedKEnd s t B sp Z op up k 0 0 none
  | some (true, rest) => SharedKEnd s t B sp Z op up k 1 (r.length - rest.length) (some c)
  | some (false, rest) => SharedKEnd s t B sp Z op up k 3 (r.length - rest.length) none

/-- `montSetup`, `millerRabinWith` and `mrResult`, for the candidate `c` in
`aN`, from offset `8 w` of `rand`. -/
theorem sharedKTail_ok (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hmc : MmCalls M mm) (R : Kernel) {s : State} {B sp : Addr} {Z w : Nat} {mi : BitVec 64} {c : Nat} {op up rp : Addr}
    {r : List Byte} (henv : SharedEnv B Z sp s) (hZ28 : slot w 28 ≤ Z) (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z) (hXZ : slot w aRm1 + 8 * (w + 2) ≤ Z) (hw4 : 4 ≤ w)
    (hw64 : w ≤ 64) (hn : wv s.mem B (slot w aN) w = c) (hsh : VG.Proof.RsaKeyGen.PrimeShape (64 * w) c)
    (ho : OutUp s B Z op up (8 * w)) (hO : word s.mem B (8 * kOut) = op)
    (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w)) (hU : word s.mem B (8 * kUsedP) = up)
    (hrp : word s.mem B (8 * kRand) = rp) (hrlen : word s.mem B (8 * kRandLen) = BitVec.ofNat 64 r.length)
    (hus : word s.mem B (8 * kUsed) = BitVec.ofNat 64 (8 * w)) (hsrc : Src s B Z rp r) (hrl : r.length < 2 ^ 64)
    (hrk : 8 * w ≤ r.length) :
    WP isa (seqs (montSetup mm ++ expSetup ++ millerRabinWith mm R.run ++ [mrResult])) s fun t =>
      SharedTestEnd s t B sp Z op up (8 * w) r c (Spec.RsaKeyGen.primalityTest c (r.drop (8 * w))) := by
  have hnw := hg.scr.nowrap
  obtain hd : MrDims B Z w := ⟨hZ, hXZ, hw4, by omega_arith⟩
  obtain ⟨hodd, hlo, hhi⟩ := hsh
  obtain htop : 2 ^ (64 * w - 1) ≤ c := by
    have : 2 ^ (64 * w - 1) = 2 ^ (64 * w - 2) * 2 := by rw [← Nat.pow_succ]; congr 1; omega_arith
    omega_arith
  obtain hc1 : 1 < c := by
    have : 2 ≤ 2 ^ (64 * w - 1) := Nat.le_trans (by decide) (Nat.pow_le_pow_right (by decide) (show 1 ≤ 64 * w - 1 by omega_arith))
    omega_arith
  rw [List.append_assoc, List.append_assoc]
  refine wp_seqs_append (by simp [montSetup]) (by simp [expSetup, lowWord]) ?_
  refine WP.mono (montSetup_call_ok M hmc henv hg hZ hXZ hw4 hw64 hn hodd htop) fun s₀ ⟨mi', hg₀, hinv₀, hr2₀, hr1₀, hrm₀, hch₀,
    hf₀, k₀⟩ => ?_
  obtain hn₀ : wv s₀.mem B (slot w aN) w = c := by
    rw [SharedFrame.array hf₀ henv (d := slot w aN) (k := w) (by simp only [msRanges]; rng_disj)
      (by have := slot_le (w := w) (show aN < 8 by decide); omega_arith) hnw]; exact hn
  refine wp_seqs_append (by simp [expSetup, lowWord]) (by simp [millerRabinWith]) ?_
  refine WP.mono (expSetup_ok hg₀ hd hn₀ hodd hc1) fun s₁ ⟨hE₁, hfE, hg₁, kEx⟩ => ?_
  obtain hf₁ : SharedFrame B sp (msRanges w ++ [(slot w aE, 8 * (w + 1))]) s.mem s₁.mem :=
    (hf₀.mono fun r hr => List.mem_append_left _ hr).trans (hfE.work.mono fun r hr => List.mem_append_right _ hr)
  obtain k₁ : Keep mmRegs s s₁ := (k₀.trans kEx).mono (by decide)
  obtain hEw : ∀ {d k : Nat}, d + 8 * k ≤ slot w aE ∨ slot w aE + 8 * (w + 1) ≤ d → d + 8 * k ≤ 2 ^ 64 →
      wv s₁.mem B d k = wv s₀.mem B d k := fun h h' => hfE.wv_eq (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h) h'
  obtain hinv₁ : ((word s₁.mem B (slot w aN)).toNat * mi'.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hfE.word_eq (d := slot w aN) (by rng_disj) (by have := slot_le (w := w) (show aN < 8 by decide); omega_arith)]
    exact hinv₀
  obtain hr2₁ : wv s₁.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c := by
    rw [hEw (Or.inl (by simp only [slot, hdrBytes, aR2, aE]; omega_using [])) (by have := slot_le (w := w) (show aR2 < 8 by decide); omega_arith)]; exact hr2₀
  obtain hr1₁ : wv s₁.mem B (slot w aR1) w = 2 ^ (64 * w) % c := by
    rw [hEw (Or.inr (by simp only [slot, hdrBytes, aR1, aE]; omega_using [])) (by unfold slot aR1 aRm1 at *; omega_arith)]; exact hr1₀
  obtain hrm₁ : wv s₁.mem B (slot w aRm1) w = c - 2 ^ (64 * w) % c := by
    rw [hEw (Or.inr (by simp only [slot, hdrBytes, aRm1, aE]; omega_using [])) (by omega_arith)]; exact hrm₀
  obtain hch₁ : word s₁.mem B (8 * kChecks) = BitVec.ofNat 64 (checksW w) := by
    rw [hfE.word_eq (d := 8 * kChecks) (by rng_disj) (by unfold kChecks kE sFn; omega_arith)]; exact hch₀
  obtain hw₁ : ∀ {k}, k = kRand ∨ k = kLen ∨ k = kRandLen ∨ k = kUsed ∨ k = kOut ∨ k = kUsedP →
      word s₁.mem B (8 * k) = word s.mem B (8 * k) := fun {k} hk => by
    obtain hk32 : k < 32 := by rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    obtain hd : ∀ r ∈ msRanges w ++ [(slot w aE, 8 * (w + 1))], 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
      simp only [msRanges, List.cons_append, List.nil_append]
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> rng_disj
    exact SharedFrame.word hf₁ henv hd (by have := hdr_lt_slot w 8 hk32; omega_arith) hnw
  obtain hsl₁ : ∀ r ∈ msRanges w ++ [(slot w aE, 8 * (w + 1))], r.1 + r.2 ≤ Z := fun r hr => by
    have : r.1 + r.2 ≤ slot w aRm1 + 8 * (w + 2) := by
      revert r hr; simp only [msRanges, List.cons_append, List.nil_append]; rng_le
    omega_arith
  obtain hc₁ : MrCtx s₁ B Z w mi' c (wv s₁.mem B (slot w aB) w) :=
    ⟨hg₁, hinv₁, by rw [hfE.wv_eq (d := slot w aN) (k := w) (by rng_disj)
      (by have := slot_le (w := w) (show aN < 8 by decide); omega_arith)]; exact hn₀, rfl, hr1₁, hrm₁⟩
  obtain hsrc₁ := hsrc.shared henv hf₁ hsl₁ k₁
  obtain hres : mrRest c (checksW w) r 1 0 (8 * w) = Spec.RsaKeyGen.primalityTest c (r.drop (8 * w)) := by
    rw [VG.Proof.RsaKeyGen.primalityTest_cand (by omega_arith) ⟨hodd, hlo, hhi⟩, checksW_eq w (by omega_arith) hw4]
  refine wp_seqs_append (by simp [millerRabinWith]) (by simp) ?_
  refine WP.mono (sharedMillerRabin_ok M hmc R hd hZ28 hc1 ⟨hodd, hlo, hhi⟩ hrl (Nat.lt_of_le_of_lt (checksW_le w) (by decide)) (henv.kept k₁ (by decide)) hc₁ hE₁ hr2₁
    (by rw [hw₁ (Or.inl rfl)]; exact hrp) (by rw [hw₁ (Or.inr (Or.inl rfl))]; exact hK)
    (by rw [hw₁ (Or.inr (Or.inr (Or.inl rfl)))]; exact hrlen) hch₁ hsrc₁
    (by rw [hw₁ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]; exact hus) (Nat.le_refl _) hrk)
    fun s₂ ⟨⟨bm, hc₂⟩, h0, h1, hf₂, k₂⟩ => ?_
  rw [hres] at h0 h1
  obtain hw₂ : ∀ {k}, k = kRand ∨ k = kLen ∨ k = kRandLen ∨ k = kUsed ∨ k = kOut ∨ k = kUsedP →
      k ≠ kUsed → word s₂.mem B (8 * k) = word s.mem B (8 * k) := fun {k} hk hku => by
    obtain hk32 : k < 32 := by rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [← hw₁ hk]
    refine SharedFrame.word hf₂ henv (sharedRoundRanges_hdr w ?_)
      (by have := hdr_lt_slot w 8 hk32; omega_arith) hnw
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact absurd rfl hku | simp only [true_or, or_true]
  obtain hsl₂ : ∀ r ∈ sharedRoundRanges w, r.1 + r.2 ≤ Z := fun r hr => by
    have := sharedRoundRanges_le w r hr; omega_arith
  obtain hhi : ∀ x, ¬(below sp 128).Contains x 1 → Z ≤ ofs B x → s₂.mem x = s.mem x := by
    intro x he hx
    apply Eq.trans (hf₂ x (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact he) (fun r hr => Or.inr (Nat.le_trans (hsl₂ r hr) hx)))
    exact hf₁ x (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact he) (fun r hr => Or.inr (Nat.le_trans (hsl₁ r hr) hx))
  obtain hout : ∀ j < 8 * w, s₂.mem (op + BitVec.ofNat 64 j) = s.mem (op + BitVec.ofNat 64 j) := by
    intro j hj
    exact hhi _ (henv.clear.miss wr_mem (ho.outw j hj) (by simp)) (ho.outZ j hj)
  obtain hlo : ∀ i < 6, word s₂.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
    obtain h2 : ∀ r ∈ sharedRoundRanges w, 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i := fun r hr => by
      have : 48 ≤ r.1 := sharedRoundRanges_low w r hr
      omega_arith
    obtain h1' : ∀ r ∈ msRanges w ++ [(slot w aE, 8 * (w + 1))], 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i := fun r hr => by
      have : 48 ≤ r.1 := by revert r hr; simp only [msRanges, List.cons_append, List.nil_append]; rng_le
      omega_arith
    rw [SharedFrame.word hf₂ henv h2 (by omega_arith) hnw, SharedFrame.word hf₁ henv h1' (by omega_arith) hnw]
  obtain k12 : Keep mmRegs s s₂ := (k₁.trans k₂).mono (by decide)
  obtain ho₂ := ho.congr (k12.2.2)
  refine WP.mono (mrResult_ok (r := r) hc₂.good hZ (by omega_arith) (by omega_arith) hc₂.n ho₂
    (by rw [hw₂ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (by decide)]; exact hO)
    (by rw [hw₂ (Or.inr (Or.inl rfl)) (by decide)]; exact hK)
    (by rw [hw₂ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) (by decide)]; exact hU) h0 h1) fun t ht => ?_
  rcases hp : Spec.RsaKeyGen.primalityTest c (r.drop (8 * w)) with _ | ⟨b, rest⟩
  · rw [hp] at ht; exact ht.shared.trans_pre hlo hhi hout k12
  · rw [hp] at ht; cases b <;> exact ht.shared.trans_pre hlo hhi hout k12

end VG.Proof.RsaKeyGen.X86_64

end

end


/-! # All candidate checks followed by the shared prepared round -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.MillerRabin.X86_64
open VG.Proof.MlKem.X86_64

theorem kMainWith_eq (mul : Nat → Nat → Nat → Prog isa) (body : Prog isa) : kMainWith mul body =
    seqs (loadC ++ (closeCheck ++ ([.ite .ne (finUsed 2) (seqs (trial ++
      ([.ite .ne (finUsed 3) (seqs (gcdCheck ++
        ([.ite .ne (finUsed 3) (seqs (montSetup mul ++ expSetup ++ millerRabinWith mul body ++ [mrResult]))] : List (Prog isa))))] : List (Prog isa))))] : List (Prog isa)))) := by
  unfold kMainWith; rw [List.append_assoc]

/-- `kMainWith`. -/
theorem sharedKMain_ok (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hmc : MmCalls M mm) (R : Kernel) {s : State} {B sp : Addr} {Z w : Nat} {op up eP pP rP : Addr} {eB pB r : List Byte}
    (henv : SharedEnv B Z sp s) (hZ28 : slot w 28 ≤ Z) (h : MainCtx s B Z (8 * w) op up eP pP rP eB pB r) :
    WP isa (kMainWith mm R.run) s fun t => SharedCandEnd s t B sp Z op up (8 * w) r
      (VG.Proof.RsaKeyGen.afterDraw (64 * w) (Spec.Rsa.os2ip eB) (Spec.RsaKeyGen.otherPrime pB)
        (Spec.RsaKeyGen.candidate (64 * w) (Spec.Rsa.os2ip (r.take (8 * w)))) (r.drop (8 * w))) := by
  have hs := h.scr
  have hn := hs.nowrap
  have hk1 := h.k1
  have hk2 := h.k2
  obtain hw8 : 8 * w / 8 = w := by omega_arith
  have hTZ := h.z
  rw [hw8] at hTZ
  obtain hZ : slot w 8 ≤ Z := by unfold slot aTab at *; omega_arith
  obtain hl8 : 8 * 32 ≤ Z := by have := hdr_lt_slot w 8 (show 31 < 32 by decide); omega_arith
  rw [kMainWith_eq]
  refine wp_seqs_append (by simp [loadC]) (by simp [closeCheck]) ?_
  -- The candidate.
  obtain hsrcr : Src s B Z rP (r.take (8 * w)) := by
    have := VG.Proof.RsaKeyGen.X86_64.Src.seg h.rsrc (a := 0) (n := 8 * w) (by have := h.rk; omega_arith)
    rwa [seg_zero, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at this
  refine WP.mono (loadC_ok hs h.rdi (by rw [hw8]; exact hZ) (by omega_arith) (by omega_arith) (by omega_arith) h.len h.rand hsrcr
    (by simp; have := h.rk; omega_arith)) fun s₁ ⟨hc₁, hus₁, hsw₁, harr₁, hf₁, hdi₁, h12₁, k₁⟩ => ?_
  rw [hw8, show 8 * (8 * w) = 64 * w by omega_arith] at hc₁
  rw [hw8] at hsw₁ harr₁ hf₁
  generalize hcv : Spec.RsaKeyGen.candidate (64 * w) (Spec.Rsa.os2ip (r.take (8 * w))) = c at hc₁ ⊢
  obtain hsh : VG.Proof.RsaKeyGen.PrimeShape (64 * w) c := hcv ▸ VG.Proof.RsaKeyGen.candidate_shape (by omega_arith) _
  obtain hg₁ : Good s₁ B Z w (word s₁.mem B (8 * sMinv)) := ⟨hs.congr k₁.2.2, hdi₁, ⟨hsw₁, rfl, harr₁⟩⟩
  obtain hh₁ : ∀ {i}, i = kOut ∨ i = kLen ∨ i = kUsedP ∨ i = kE ∨ i = kElen ∨ i = kP ∨ i = kPlen ∨ i = kRand ∨
      i = kRandLen → word s₁.mem B (8 * i) = word s.mem B (8 * i) := fun {i} hi => by
    obtain hi32 : i < 32 := by rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    refine hf₁.word_eq ?_ (by omega_arith)
    simp only [loadCRanges]
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rng_disj
  obtain hin₁ : InScr B Z s.mem s₁.mem := InScr.of_frm hf₁ (by simp only [loadCRanges]; rng_le)
  obtain hsv₁ : ∀ i < 6, word s₁.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    hf₁.word_eq (fun r hr => Or.inl (by revert r hr; simp only [loadCRanges]; rng_le)) (by omega_arith)
  obtain st₁ : (∀ i ≤ 25, word s₁.mem B (8 * i) = word s₁.mem B (8 * i)) ∧ InScr B Z s₁.mem s₁.mem :=
    ⟨fun _ _ => rfl, InScr.refl _ _ _⟩
  obtain ho₁ := h.ou.congr k₁.2.2
  -- Too close to `p`.
  refine wp_seqs_append (by simp [closeCheck]) (by simp) ?_
  refine WP.mono (closeCheck_ok hg₁ hZ (by omega_arith) (by omega_arith) (by rw [hh₁ (by simp)]; exact h.p)
    (by rw [hh₁ (by simp)]; exact h.len) (by rw [hh₁ (by simp)]; exact h.plen) h.pl (h.psrc.congrK hin₁ k₁))
    fun s₂ ⟨hz₂, hg₂, hf₂, k₂⟩ => ?_
  rw [hc₁] at hz₂
  obtain st₂ := stage hf₂ (by simp only [closeRanges]; rng_le) (fun r hr => by
    have : r.1 + r.2 ≤ slot w 8 := by revert r hr; simp only [closeRanges]; rng_le
    omega_arith) st₁
  obtain k12 : Keep mmRegs s s₂ := (k₁.trans k₂).mono (by decide)
  obtain hsv₂ : ∀ i < 6, word s₂.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    (st₂.1 i (by omega_arith)).trans (hsv₁ i hi)
  obtain hin₂ : InScr B Z s.mem s₂.mem := hin₁.trans st₂.2
  obtain hk₂ : ∀ {i}, i = kOut ∨ i = kLen ∨ i = kUsedP ∨ i = kE ∨ i = kElen ∨ i = kP ∨ i = kPlen ∨ i = kRand ∨
      i = kRandLen → word s₂.mem B (8 * i) = word s.mem B (8 * i) := fun {i} hi => by
    have : i ≤ 25 := by rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [st₂.1 i this, hh₁ hi]
  obtain hu₂ : word s₂.mem B (8 * kUsed) = BitVec.ofNat 64 (8 * w) := by rw [st₂.1 kUsed (by decide), hus₁]
  refine WP.ite (Spec.RsaKeyGen.tooClose (64 * w) (Spec.RsaKeyGen.otherPrime pB) c) (by simp [eval, hz₂])
    (fun hcl => ?_) (fun hcl => ?_)
  · refine WP.mono (sharedFinUsed_end (sp := sp) hg₂.scr hg₂.rdi hl8 (by decide) hu₂ (by rw [hk₂ (by simp)]; exact h.usedP)
      (h.ou.congr k12.2.2) hsv₂ hin₂ k12) fun t ht => ?_
    unfold VG.Proof.RsaKeyGen.afterDraw
    rw [hcl]
    simp only [↓reduceIte, SharedCandEnd, List.length_drop]
    rwa [show r.length - (r.length - 8 * w) = 8 * w by have := h.rk; omega_arith]
  obtain hc₂ : wv s₂.mem B (slot w aN) w = c := by
    rw [hf₂.wv_eq (d := slot w aN) (k := w) (by simp only [closeRanges]; rng_disj)
      (by have := slot_le (w := w) (show aN < 8 by decide); omega_arith)]; exact hc₁
  obtain hgt : 8161 < c := by
    obtain ⟨_, hlo, _⟩ := hsh
    have : 2 ^ 13 ≤ 2 ^ (64 * w - 2) := Nat.pow_le_pow_right (by decide) (by omega_arith)
    omega_arith
  obtain hend : ∀ {sX : State} {mi : BitVec 64}, Good sX B Z w mi → Keep mmRegs s sX →
      (∀ i ≤ 25, word sX.mem B (8 * i) = word s₁.mem B (8 * i)) → InScr B Z s₁.mem sX.mem →
      WP isa (finUsed 3) sX fun t => SharedKEnd s t B sp Z op up (8 * w) 3 (8 * w) none := by
    intro sX mi hgX kX hX hinX
    exact sharedFinUsed_end (sp := sp) hgX.scr hgX.rdi hl8 (by decide) (by rw [hX kUsed (by decide), hus₁])
      (by rw [hX kUsedP (by decide), hh₁ (by simp)]; exact h.usedP) (h.ou.congr kX.2.2)
      (fun i hi => (hX i (by omega_arith)).trans (hsv₁ i hi)) (hin₁.trans hinX) kX
  obtain hrej : ∀ t, SharedKEnd s t B sp Z op up (8 * w) 3 (8 * w) none → SharedCandEnd s t B sp Z op up (8 * w) r
      (some (.rejected, r.drop (8 * w))) := fun t ht => by
    simp only [SharedCandEnd, List.length_drop]
    rwa [show r.length - (r.length - 8 * w) = 8 * w by have := h.rk; omega_arith]
  -- Trial division.
  refine wp_seqs_append (by simp [trial]) (by simp) ?_
  refine WP.mono (trial_ok hg₂ hZ hTZ (by omega_arith) (by omega_arith)) fun s₃ ⟨hz₃, hg₃, hf₃, k₃⟩ => ?_
  rw [hc₂, trialAny_eq hgt] at hz₃
  obtain st₃ := stage hf₃ (by rng_le) (fun r hr => by
    have : r.1 + r.2 ≤ slot w aTab + 2048 := by revert r hr; rng_le
    omega_arith) st₂
  obtain k13 : Keep mmRegs s s₃ := (k12.trans k₃).mono (by decide)
  refine WP.ite (Spec.RsaKeyGen.obviouslyComposite (64 * w) c) (by simp [eval, hz₃]) (fun hoc => ?_) (fun hoc => ?_)
  · refine WP.mono (hend hg₃ k13 st₃.1 st₃.2) fun t ht => ?_
    unfold VG.Proof.RsaKeyGen.afterDraw
    simp only [hcl, hoc, Bool.false_eq_true, ↓reduceIte, Bool.not_true, Bool.false_and]
    exact hrej t ht
  obtain hc₃ : wv s₃.mem B (slot w aN) w = c := by
    rw [hf₃.wv_eq (d := slot w aN) (k := w) (by rng_disj)
      (by have := slot_le (w := w) (show aN < 8 by decide); omega_arith)]; exact hc₂
  obtain hk₃ : ∀ {i}, i = kOut ∨ i = kLen ∨ i = kUsedP ∨ i = kE ∨ i = kElen ∨ i = kP ∨ i = kPlen ∨ i = kRand ∨
      i = kRandLen → word s₃.mem B (8 * i) = word s.mem B (8 * i) := fun {i} hi => by
    have : i ≤ 25 := by rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [st₃.1 i this, hh₁ hi]
  -- `gcd(c − 1, e)`.
  refine wp_seqs_append (by simp [gcdCheck, loadE]) (by simp) ?_
  refine WP.mono (gcdCheck_ok hg₃ hZ (by omega_arith) (by omega_arith) (by rw [hc₃]; exact hsh.1)
    (by rw [hc₃]; omega_arith) (by rw [hk₃ (by simp)]; exact h.e) (by rw [hk₃ (by simp)]; exact h.elen) h.el1 h.el8
    (h.esrc.congrK (hin₁.trans st₃.2) k13)) fun s₄ ⟨hz₄, hg₄, hf₄, k₄⟩ => ?_
  rw [hc₃] at hz₄
  obtain st₄ := stage hf₄ (by rng_le) (fun r hr => by
    have : r.1 + r.2 ≤ slot w 8 := by revert r hr; rng_le
    omega_arith) st₃
  obtain k14 : Keep mmRegs s s₄ := (k13.trans k₄).mono (by decide)
  refine WP.ite (!decide (Nat.gcd (c - 1) (Spec.Rsa.os2ip eB) = 1)) (by simp [eval, hz₄]) (fun hgc => ?_)
    (fun hgc => ?_)
  · refine WP.mono (hend hg₄ k14 st₄.1 st₄.2) fun t ht => ?_
    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hgc
    unfold VG.Proof.RsaKeyGen.afterDraw
    simp only [hcl, hoc, hgc, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and, beq_iff_eq]
    exact hrej t ht
  simp only [Bool.not_eq_false', decide_eq_true_eq] at hgc
  obtain hc₄ : wv s₄.mem B (slot w aN) w = c := by
    rw [hf₄.wv_eq (d := slot w aN) (k := w) (by rng_disj)
      (by have := slot_le (w := w) (show aN < 8 by decide); omega_arith)]; exact hc₃
  obtain hk₄ : ∀ {i}, i = kOut ∨ i = kLen ∨ i = kUsedP ∨ i = kE ∨ i = kElen ∨ i = kP ∨ i = kPlen ∨ i = kRand ∨
      i = kRandLen → word s₄.mem B (8 * i) = word s.mem B (8 * i) := fun {i} hi => by
    have : i ≤ 25 := by rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [st₄.1 i this, hh₁ hi]
  have hXZ := h.zx
  rw [hw8] at hXZ
  refine WP.mono (sharedKTail_ok M hmc R (henv.kept k14 (by decide)) hZ28 hg₄ hZ hXZ (by omega_arith) (by omega_arith) hc₄ hsh (h.ou.congr k14.2.2)
    (by rw [hk₄ (by simp)]; exact h.out) (by rw [hk₄ (by simp)]; exact h.len) (by rw [hk₄ (by simp)]; exact h.usedP)
    (by rw [hk₄ (by simp)]; exact h.rand) (by rw [hk₄ (by simp)]; exact h.rlen)
    (by rw [st₄.1 kUsed (by decide), hus₁]) (h.rsrc.congrK (hin₁.trans st₄.2) k14) h.rl h.rk) fun t ht => ?_
  obtain hlo : ∀ i < 6, word s₄.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    (st₄.1 i (by omega_arith)).trans (hsv₁ i hi)
  obtain hhi : ∀ x, Z ≤ ofs B x → s₄.mem x = s.mem x := fun x hx => ((hin₁.trans st₄.2) x hx)
  unfold VG.Proof.RsaKeyGen.afterDraw
  simp only [hcl, hoc, hgc, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and, beq_self_eq_true]
  rcases hp : Spec.RsaKeyGen.primalityTest c (r.drop (8 * w)) with _ | ⟨b, rest⟩
  · rw [hp] at ht; exact SharedKEnd.trans_pre ht hlo (fun x _ hx => hhi x hx) (fun j hj => hhi _ (h.ou.outZ j hj)) k14
  · rw [hp] at ht
    cases b
    · exact SharedKEnd.trans_pre ht hlo (fun x _ hx => hhi x hx) (fun j hj => hhi _ (h.ou.outZ j hj)) k14
    · exact SharedKEnd.trans_pre ht hlo (fun x _ hx => hhi x hx) (fun j hj => hhi _ (h.ou.outZ j hj)) k14

end VG.Proof.RsaKeyGen.X86_64

end

end

/-! # Internal RSA candidate contract with room for the shared call -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64

def sharedCandPre (s : State) : Prop :=
  candPre s ∧ SharedEnv (arg s 3) ((arg s 4).toNat * 8) (s.gpr .rsp) s

def sharedCandContract : Contract isa where
  pre := sharedCandPre
  post := candPost
  pub := candPub

end VG.Proof.RsaKeyGen.X86_64
